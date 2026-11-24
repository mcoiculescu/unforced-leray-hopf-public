import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ReflectResidual
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CellNeg

/-!
# Part I, task `PartI:T02/3` (helper): the reflected pair is a classical solution

Source of record: `the November 2 reference manuscript`, line 288 ("Uniqueness gives
`v(-q,-eta,s) = -v(q,eta,s)`"). The reflected pair `(reflV v, reflP p) = (-v(s,-z), p(s,-z))` is a
classical solution on `[0,T]` with the same datum `trainDatum c`, which is centrally odd
(`B0140.trainDatum_neg`).

The fields of `IsClassicalOn` are handled as follows:

* smoothness: composition with the map `(s,z) ↦ (s,-z)`, which sends `Icc 0 T ×ˢ univ` into itself;
* periodicity: `z ↦ -z` sends the shift `(z.1 + c, z.2)` to `(-z.1 - c, -z.2)`;
* solenoidal and momentum: `reflect_residual_identities`;
* initial datum: `trainDatum_neg`;
* finite energy: `integrableOn_cell_neg`.

All helper names carry the prefix `rc`.
-/

namespace UnforcedLeray.Short.PartI

open Set Filter MeasureTheory
open scoped ContDiff Topology

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0140 (trainDatum)

/-- Composition with `(s,z) ↦ (s,-z)` preserves smoothness on `Icc 0 T ×ˢ univ`. -/
theorem rc_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    {w : ℝ × Plane → E} (hw : ContDiffOn ℝ ∞ w (Icc 0 T ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w (x.1, -x.2)) (Icc 0 T ×ˢ univ) := by
  have hmap : ContDiff ℝ ∞ (fun x : ℝ × Plane => (x.1, -x.2)) :=
    contDiff_fst.prodMk contDiff_snd.neg
  have hmaps : MapsTo (fun x : ℝ × Plane => (x.1, -x.2)) (Icc 0 T ×ˢ univ) (Icc 0 T ×ˢ univ) := by
    intro x hx
    exact Set.mk_mem_prod hx.1 (Set.mem_univ _)
  exact hw.comp hmap.contDiffOn hmaps

/-- Negation of a `c`-periodic function is `c`-periodic. -/
theorem rc_periodic_neg {E : Type*} [AddCommGroup E] {c : ℝ} {g : Plane → E}
    (hg : Cyl.IsPeriodic c g) : Cyl.IsPeriodic c (fun z => -g z) := by
  intro z
  show -g (z.1 + c, z.2) = -g z
  rw [hg z]

/-- Precomposition with `z ↦ -z` preserves `c`-periodicity in the first coordinate. -/
theorem rc_periodic_comp_neg {E : Type*} {c : ℝ} {f : Plane → E}
    (hf : Cyl.IsPeriodic c f) : Cyl.IsPeriodic c (fun z => f (-z)) := by
  intro z
  have h : f (-z.1, -z.2) = f (-z.1 - c, -z.2) := by
    have h0 := hf (-z.1 - c, -z.2)
    simp only [sub_add_cancel] at h0
    exact h0
  have e1 : -((z.1 + c, z.2) : Plane) = (-z.1 - c, -z.2) :=
    Prod.ext (by simp only [Prod.fst_neg]; ring) (by simp only [Prod.snd_neg])
  have e2 : -z = (-z.1, -z.2) := Prod.ext (by simp only [Prod.fst_neg]) (by simp only [Prod.snd_neg])
  show f (-((z.1 + c, z.2) : Plane)) = f (-z)
  rw [e1, e2]
  exact h.symm

/-- The reflected pair of a classical solution is a classical solution with the same datum
(source line 288; `B0140.trainDatum_neg` for the datum). -/
theorem reflectClassical : ReflectClassical := by
  intro ν c T v p hν hc hT hcl
  exact
    { smooth_v := (rc_smooth_comp hcl.smooth_v).neg
      smooth_p := rc_smooth_comp hcl.smooth_p
      periodic_v := fun s hs => rc_periodic_neg (rc_periodic_comp_neg (hcl.periodic_v s hs))
      periodic_p := fun s hs => rc_periodic_comp_neg (hcl.periodic_p s hs)
      solenoidal := fun s hs z => by
        rw [(reflect_residual_identities ν v p s z).2]
        exact hcl.solenoidal s hs (-z)
      momentum := fun s hs z => by
        rw [(reflect_residual_identities ν v p s z).1, hcl.momentum s hs (-z), neg_zero]
      initial := by
        funext z
        show -v 0 (-z) = trainDatum c z
        rw [hcl.initial, UnforcedLeray.B0140.trainDatum_neg, neg_neg]
      finite_energy := fun s hs => by
        have h := integrableOn_cell_neg (f := fun z => ‖v s z‖ ^ 2) (hcl.finite_energy s hs)
        have e : (fun z : Plane => ‖reflV v s z‖ ^ 2)
            = fun z : Plane => (fun z => ‖v s z‖ ^ 2) (-z) := by
          funext z
          show ‖-v s (-z)‖ ^ 2 = ‖v s (-z)‖ ^ 2
          rw [norm_neg]
        rw [e]
        exact h }

end UnforcedLeray.Short.PartI
