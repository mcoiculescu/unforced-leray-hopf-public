import UnforcedLeray.Short.PartI.Sub.C03

/-!
# Part I, leaf `PartI:C03/4`: the Dyson bridge (`DysonBridge`)

Source of record: `the November 2 reference manuscript`, lines 1031-1049
(Dyson series of the evolutions fed to Lemma `short-compact-duhamel`).

For every block start `s`, the hypothesis supplies an `Evolution.EvolutionFamily` `E s` on
`[s, s+B]` and a bounded perturbation `Ap s` with interaction `A`, such that `E s` agrees with
`F` on the triangle and `Evolution.dyson (E s) (Ap s)` agrees with `U` on the triangle. The
`B0104` Dyson iterates of `(F, A)` coincide with those of `(E s, Ap s)` on the triangle
(induction on the order `k`). Hence the iterated integrands are interval integrable
(`Evolution.EvolutionFamily.intervalIntegrable_integrand`), and the Dyson series converges to `U`
(`Evolution.hasSum_dyson`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- Block key lemma: on one block `[s, s+B]`, the `B0104` Dyson iterates of `(F, A)` coincide
with the `Evolution` Dyson iterates of `(E, Ap)` on the triangle `s ≤ u ≤ v ≤ s+B`. -/
theorem dysonBridge_block (F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG)
    (A : ℝ → B0010.XG →L[ℂ] B0010.XG) (s B : ℝ)
    (E : UnforcedLeray.Evolution.EvolutionFamily B0010.XG s (s + B))
    (Ap : UnforcedLeray.Evolution.BoundedPert B0010.XG s (s + B))
    (hA : ∀ r, Ap.A r = A r)
    (hE : ∀ u v, s ≤ u → u ≤ v → v ≤ s + B → E.U v u = F v u) :
    ∀ (k : ℕ) (u v : ℝ), s ≤ u → u ≤ v → v ≤ s + B → ∀ x : B0010.XG,
      B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () v u x =
        UnforcedLeray.Evolution.dysonTerm E Ap k v u x := by
  intro k
  induction k with
  | zero =>
    intro u v hu huv hv x
    show F v u x = UnforcedLeray.Evolution.dysonTerm E Ap 0 v u x
    rw [UnforcedLeray.Evolution.dysonTerm_zero, hE u v hu huv hv]
  | succ k ih =>
    intro u v hu huv hv x
    show (∫ r in u..v, F v r (A r (B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k ()
        r u x))) = UnforcedLeray.Evolution.dysonTerm E Ap (k + 1) v u x
    rw [UnforcedLeray.Evolution.dysonTerm_succ]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le huv] at hr
    show F v r (A r (B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () r u x)) =
      E.U v r (Ap.A r (UnforcedLeray.Evolution.dysonTerm E Ap k r u x))
    rw [hE r v (hu.trans hr.1) hr.2 hv, hA r, ih u r hu hr.1 (hr.2.trans hv) x]

/-- **Leaf 4** (`DysonBridge`; source lines 1031-1049): the bridge from evolution families to the
`B0104` Dyson predicates `DysonDefined` and `IsDysonSum`, with index set `Unit`. -/
theorem dysonBridge : DysonBridge := by
  intro B F U A h
  choose E Ap hA hE hU using h
  have key : ∀ s : ℝ, ∀ (k : ℕ) (u v : ℝ), s ≤ u → u ≤ v → v ≤ s + B → ∀ x : B0010.XG,
      B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () v u x =
        UnforcedLeray.Evolution.dysonTerm (E s) (Ap s) k v u x :=
    fun s => dysonBridge_block F A s B (E s) (Ap s) (hA s) (hE s)
  refine ⟨?_, ?_⟩
  · intro k p s t hst hts x
    have hp : p = () := Subsingleton.elim _ _
    subst hp
    have hcont : ContinuousOn (fun r => UnforcedLeray.Evolution.dysonTerm (E s) (Ap s) k r s x)
        (Icc s t) :=
      (UnforcedLeray.Evolution.continuousOn_dysonTerm_fst (E s) (Ap s) k x (le_refl s)).mono
        (Icc_subset_Icc (le_refl s) hts)
    have hint := UnforcedLeray.Evolution.EvolutionFamily.intervalIntegrable_integrand (E s) (Ap s)
      (le_refl s) hst hts hcont
    refine IntervalIntegrable.congr ?_ hint
    intro r hr
    rw [uIoc_of_le hst] at hr
    show (E s).U t r ((Ap s).A r (UnforcedLeray.Evolution.dysonTerm (E s) (Ap s) k r s x)) =
      F t r (A r (B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () r s x))
    rw [hE s r t hr.1.le hr.2 hts, hA s r, key s k s r (le_refl s) hr.1.le (hr.2.trans hts) x]
  · intro p t s hst hts x
    have hp : p = () := Subsingleton.elim _ _
    subst hp
    have h2 := UnforcedLeray.Evolution.hasSum_dyson (E s) (Ap s) ⟨le_refl s, hst, hts⟩ x
    rw [hU s s t (le_refl s) hst hts] at h2
    have hfun : (fun k => B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () t s x) =
        fun k => UnforcedLeray.Evolution.dysonTerm (E s) (Ap s) k t s x :=
      funext fun k => key s k s t (le_refl s) hst hts x
    show HasSum (fun k => B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () t s x)
      (U t s x)
    rw [hfun]
    exact h2

end UnforcedLeray.Short.PartI
