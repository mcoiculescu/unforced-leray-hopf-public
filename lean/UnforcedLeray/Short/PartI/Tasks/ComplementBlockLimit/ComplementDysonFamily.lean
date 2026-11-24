import UnforcedLeray.Short.PartI.Sub.C03
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.Stability
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalDysonRegroup

/-!
# Target `PartI:C03/6`: `complementDysonFamily`

Source of record: `the November 2 reference manuscript`, lines 1014-1030
(the complementary evolution is the Dyson sum of the free evolution `F_β` with the interaction
`A - P + β R_f`). This file proves the `Prop` `ComplementDysonFamily` of `Short/PartI/Sub/C03.lean`
with no extra hypothesis.

Method. Fix `[a,b]`, the free family `K := fdsFam a b ..` and the free interaction
`C := fdsA lam κ a b ..` (`Tasks/FreeDiffusionEvolution/Stability.lean`), where `κ = seedKappa`.

1. `U` is the Dyson sum of `(K, C + A_β)` on the triangle: its Duhamel identity
   `U(t,s)x = e^{D∫β}x + ∫ e^{D∫_r^t β} G_β(r) U(r,s)x dr` has generator
   `G_β(r) = freeCoeff(r) + complementInteraction(r)` (`complementDyson_gen`), and
   `Evolution.dyson_unique` applies.
2. `Evolution.dyson_sum_regroup` gives `dyson K (C + A_β) = dyson (dyson K C) A_β`.
3. The free evolution `F` is `dyson K C` on the triangle (`Evolution.dyson_unique`, as in
   `freeEvolutionFamily`), so `dyson K C` agrees with `E` there; the base change
   `complementDyson_baseCongr` (a copy of `dyson_base_congr` on a general block) then gives
   `dyson (dyson K C) A_β = dyson E A_β` on the triangle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Infra.Dunford (rankOneProj)

/-- Base change on a general block: two evolution families that agree on the triangle of `[a,b]`
have Dyson sums with the same bounded interaction that agree on the triangle. -/
theorem complementDyson_baseCongr {a b : ℝ}
    (F G : UnforcedLeray.Evolution.EvolutionFamily B0010.XG a b)
    (A : UnforcedLeray.Evolution.BoundedPert B0010.XG a b)
    (hFG : ∀ s t, a ≤ s → s ≤ t → t ≤ b → F.U t s = G.U t s) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (UnforcedLeray.Evolution.dyson F A).U t s = (UnforcedLeray.Evolution.dyson G A).U t s := by
  intro s t hs hst ht
  apply ContinuousLinearMap.ext
  intro x
  let V : UnforcedLeray.Evolution.EvolutionFamily B0010.XG a b :=
    UnforcedLeray.Evolution.dyson F A
  have hcont : ∀ u, a ≤ u → u ≤ b → ∀ y : B0010.XG,
      ContinuousOn (fun τ => V.U τ u y) (Icc u b) := by
    intro u hu _ y
    exact V.continuousOn_fst hu y
  have heq : ∀ u v, a ≤ u → u ≤ v → v ≤ b → ∀ y : B0010.XG,
      V.U v u y = G.U v u y + ∫ r in u..v, G.U v r (A.A r (V.U r u y)) := by
    intro u v hu huv hv y
    have hleft := UnforcedLeray.Evolution.dyson_left (F := F) (A := A) ⟨hu, huv, hv⟩ y
    calc
      V.U v u y = F.U v u y + ∫ r in u..v, F.U v r (A.A r (V.U r u y)) := hleft
      _ = G.U v u y + ∫ r in u..v, G.U v r (A.A r (V.U r u y)) := by
        rw [hFG u v hu huv hv]
        congr 1
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le huv] at hr
        rw [hFG r v (hu.trans hr.1) hr.2 hv]
  have huniq := UnforcedLeray.Evolution.dyson_unique (F := G) (A := A) (V := V.U) hcont heq
  exact congrArg (fun L : B0010.XG →L[ℂ] B0010.XG => L x) (huniq s t hs hst ht)

/-- Operator identity: the generator `L₀ - λ - ℓ(·)q - βκ + βR_f` of `IsMildComplementEvolution`
is the free coefficient `T - λ - βκ` plus the complementary interaction `L₀ - T - P + βR_f`
(source lines 1014-1030). -/
theorem complementDyson_gen (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) (β : ℝ → ℝ) (r : ℝ) :
    (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
        (β r * κ) • (1 : B0010.XG →L[ℂ] B0010.XG) + (β r : ℂ) • Rf) =
      freeCoeff lam κ β r + complementInteraction l q Rf β r := by
  unfold freeCoeff complementInteraction complementT rankOneProj
  abel

/-- **Target `PartI:C03/6`** (source lines 1014-1030): the mild complementary evolution `U` is the
Dyson sum of the free evolution `F` (on every block `[a,b]`, through an evolution family `E`
agreeing with `F` on the triangle) and the interaction `A_β`. -/
theorem complementDysonFamily : ComplementDysonFamily := by
  intro lam q l qd hq hqd βs β hβm hβb U F hU hF a b E Ap hE hAp u v hau huv hvb
  -- the free family K and the free interaction C on the block [a,b]
  have hsum : ∀ r : ℝ,
      (UnforcedLeray.Evolution.boundedPertSum
        (fdsA lam (seedKappa l q hq) a b βs β hβm hβb) Ap).A r =
        freeCoeff lam (seedKappa l q hq) β r + Ap.A r := fun r => rfl
  -- step 1: U is the Dyson sum of (K, C + Ap)
  have h1 : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      U t s = (UnforcedLeray.Evolution.dyson (fdsFam a b βs β hβm hβb)
        (UnforcedLeray.Evolution.boundedPertSum
          (fdsA lam (seedKappa l q hq) a b βs β hβm hβb) Ap)).U t s := by
    intro s t hs hst ht
    refine UnforcedLeray.Evolution.dyson_unique (fdsFam a b βs β hβm hβb)
      (UnforcedLeray.Evolution.boundedPertSum
        (fdsA lam (seedKappa l q hq) a b βs β hβm hβb) Ap) U
      (fun s' _ _ x => (hU.cont s' x).mono Set.Icc_subset_Ici_self)
      (fun s' t' _ hst' _ x => ?_) s t hs hst ht
    rw [hU.duhamel s' t' hst' x]
    congr 1
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [hsum r, hAp r,
      ← complementDyson_gen lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β r]
    rfl
  -- step 2: regroup the bounded perturbation
  have h2 : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (UnforcedLeray.Evolution.dyson (fdsFam a b βs β hβm hβb)
        (UnforcedLeray.Evolution.boundedPertSum
          (fdsA lam (seedKappa l q hq) a b βs β hβm hβb) Ap)).U t s =
      (UnforcedLeray.Evolution.dyson
        (UnforcedLeray.Evolution.dyson (fdsFam a b βs β hβm hβb)
          (fdsA lam (seedKappa l q hq) a b βs β hβm hβb)) Ap).U t s := by
    intro s t hs hst ht
    apply ContinuousLinearMap.ext
    intro x
    exact UnforcedLeray.Evolution.dyson_sum_regroup
      (fdsFam a b βs β hβm hβb) (fdsA lam (seedKappa l q hq) a b βs β hβm hβb) Ap hs t hst ht x
  -- step 3: the free evolution F is the Dyson sum of (K, C) on the triangle
  have hFK : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      F t s = (UnforcedLeray.Evolution.dyson (fdsFam a b βs β hβm hβb)
        (fdsA lam (seedKappa l q hq) a b βs β hβm hβb)).U t s := fun s t hs hst ht =>
    UnforcedLeray.Evolution.dyson_unique (fdsFam a b βs β hβm hβb)
      (fdsA lam (seedKappa l q hq) a b βs β hβm hβb) F
      (fun s' _ _ x => (hF.cont x s').mono Set.Icc_subset_Ici_self)
      (fun s' t' _ hst' _ x => hF.duhamel s' t' hst' x) s t hs hst ht
  have hFG : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (UnforcedLeray.Evolution.dyson (fdsFam a b βs β hβm hβb)
        (fdsA lam (seedKappa l q hq) a b βs β hβm hβb)).U t s = E.U t s :=
    fun s t hs hst ht => (hFK s t hs hst ht).symm.trans (hE s t hs hst ht).symm
  have h3 := complementDyson_baseCongr
    (UnforcedLeray.Evolution.dyson (fdsFam a b βs β hβm hβb)
      (fdsA lam (seedKappa l q hq) a b βs β hβm hβb)) E Ap hFG
  rw [h1 u v hau huv hvb, h2 u v hau huv hvb]
  exact (h3 u v hau huv hvb).symm

end UnforcedLeray.Short.PartI

end
