import UnforcedLeray.Short.PartI.Sub.PartI_T08_1

/-!
# Part I, task `PartI:T08/1/3` (`qcPeriodic_proof`): `c`-periodicity of `Q_c`

Source: `the November 2 reference manuscript`, lines 326-329 (`Q_c = ∑_{i≠j} V_i ⊗ V_j`).
The Prop is `QcPeriodic` in `Sub/PartI_T08_1.lean`.

Route: `Q_c^{kl}(z) = ∑' p : {p | p.1 ≠ p.2}, isoV(z.1 - p.1 c, z.2)_k · isoV(z.1 - p.2 c, z.2)_l`.
Shifting `z.1` by `c` is the same as shifting both indices of `p` by `-1`, which maps the
off-diagonal set of `ℤ × ℤ` onto itself, so the series is reindexed by `Equiv.subtypeEquiv`.
No positivity of `ν`, `c`, `s` is needed.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartI

theorem qcPeriodic_proof : UnforcedLeray.Short.PartI.QcPeriodic := by
  intro ν c s k l
  unfold UnforcedLeray.Cyl.IsPeriodic
  intro z
  show UnforcedLeray.Train.Qc ν c s (z.1 + c, z.2) k l = UnforcedLeray.Train.Qc ν c s z k l
  simp only [UnforcedLeray.Train.Qc]
  let e : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)) ≃ ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)) :=
    Equiv.subtypeEquiv (Equiv.addRight ((-1 : ℤ), (-1 : ℤ))) (fun p => by simp)
  refine (tsum_congr fun p => ?_).trans (e.tsum_eq _)
  have h1 : ∀ n : ℤ, (z.1 + c) - (n : ℝ) * c = z.1 - ((n + -1 : ℤ) : ℝ) * c := fun n => by
    push_cast; ring
  simp only [e, Equiv.subtypeEquiv_apply, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add]
  rw [h1 (p.1.1), h1 (p.1.2)]

end UnforcedLeray.Short.PartI
