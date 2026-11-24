import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1.FiniteEnergy
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2

/-!
# `PartI:T09/5/org/1/org/c`: the summed jet energy and the vector Scheffe lemma

Source: `the November 2 reference manuscript`,
lines 270-288.  The energy identities of lines 283-286 ("approximation and transverse cutoffs then
give the velocity and vorticity energy identities") control the *sum* of the squared cell norms of
all word derivatives of order at most `j`, not each word separately.  So the norm half of the
Scheffe argument is stated for that sum (`TrainJetSumLimsup`), and the Scheffe lemma is stated for a
finite family (`ScheffeL2FamilyAt0`); together with pointwise convergence it still gives the
convergence of every single word derivative in `L²(cell)` (`trainFiniteEnergyClass_of`,
`Sub/PartI_T09_5_org_1_org_c.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The summed jet energy of a train at age `s`:
`S_j(s) = ∫_cell Σ_{|w| ≤ j} Σ_k (∂_w v_k(s))²` (a `lintegral`, so no junk value). -/
def trainJetSum {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in UnforcedLeray.Cyl.cell c,
    ENNReal.ofReal (∑ w ∈ wordsUpTo j, ∑ k : Fin 2, (wordComp w (tr.v s) k z) ^ 2)

/-- **Source fact (lines 270-288, the energy inequality at age `0` for the jets):** for a BUC train
and every order `j`, `limsup_{s→0+} S_j(s) ≤ S_j(0)`.  (Order `0`: the velocity energy identity
with transverse cutoffs; order `≥ 1`: `∫|∇g|² = ∫(curl g)²` for the divergence-free `g = ∂_u v`
and the vorticity jet energy identity.  Decomposed in `PartI_T09_5_org_1_org_c/SumLimsup.lean`.) -/
def TrainJetSumLimsup : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ j : ℕ,
    limsup (fun s : ℝ => trainJetSum tr j s) (nhdsWithin (0 : ℝ) (Ici 0)) ≤ trainJetSum tr j 0

/-- **Vector Scheffe lemma in `L²` along `s → 0+`** (measure theory).  For a finite family `F_i`
(`i ∈ I`) of functions that are continuous for `s ≥ 0` and converge pointwise as `s → 0+`, with
`F_i(0)` square integrable on `A`, if the `limsup` of `∫_A Σ_i F_i(s)²` is at most `∫_A Σ_i F_i(0)²`,
then every `F_i(s) → F_i(0)` in `L²(A)`. -/
def ScheffeL2FamilyAt0 : Prop :=
  ∀ (ι : Type) (I : Finset ι) (A : Set Plane) (F : ι → ℝ → Plane → ℝ),
    MeasurableSet A →
    (∀ i ∈ I, ∀ s : ℝ, 0 ≤ s → Continuous (F i s)) →
    (∀ i ∈ I, ∀ z : Plane,
      Tendsto (fun s : ℝ => F i s z) (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 (F i 0 z))) →
    (∀ i ∈ I, ∫⁻ z in A, ENNReal.ofReal ((F i 0 z) ^ 2) < ⊤) →
    limsup (fun s : ℝ => ∫⁻ z in A, ENNReal.ofReal (∑ i ∈ I, (F i s z) ^ 2))
        (nhdsWithin (0 : ℝ) (Ici 0)) ≤
      ∫⁻ z in A, ENNReal.ofReal (∑ i ∈ I, (F i 0 z) ^ 2) →
    ∀ i ∈ I, Tendsto (fun s : ℝ => ∫⁻ z in A, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2))
      (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0)

end UnforcedLeray.Short.PartI
