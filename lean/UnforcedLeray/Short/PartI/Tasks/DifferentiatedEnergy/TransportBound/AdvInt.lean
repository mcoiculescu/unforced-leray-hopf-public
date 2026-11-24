import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.AdvCommutator

/-!
# Part I, task `PartI:T08/7/2/1`: `JTAdvInt` (integrability of the pairing integrand)

Source: `the November 2 reference manuscript` lines 352-358.

Route: the Leibniz rule for word derivatives (`wac_gen`, `AdvCommutator.lean`) expands every word of
`advB u h` into a finite list sum over the splittings `wacSplits w` of products
`(word of u) * (word of h)`. Each product `∂_w f_k · (∂_a u_m)(∂_b h_k)` is integrable on the cell
because one of the two factors `∂_a u_m`, `∂_b h_k` lies in `L²(cell)` (hypothesis `CellSmoothL2`),
the other is bounded, and `∂_w f_k ∈ L²(cell)`; `MemLp.integrable_mul` and `Integrable.mul_bdd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Sums of list-valued integrable families are integrable. -/
theorem jai_list_integrable {μ : Measure Plane} {α : Type*} (G : α → Plane → ℝ) :
    ∀ L : List α, (∀ p ∈ L, Integrable (G p) μ) →
      Integrable (fun z => (L.map (fun p => G p z)).sum) μ
  | [], _ => by simp
  | p :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h p (by simp)).add (jai_list_integrable G L fun q hq => h q (by simp [hq]))

/-- Scalar factor pulled inside a list sum. -/
theorem jai_list_mul {α : Type*} (x : ℝ) (F : α → ℝ) :
    ∀ L : List α, x * (L.map F).sum = (L.map (fun p => x * F p)).sum
  | [] => by simp
  | a :: L => by
    simp only [List.map_cons, List.sum_cons, mul_add]
    rw [jai_list_mul x F L]

/-- Integrability of a product `x · (A · B)` of three functions on a measure, when `x` is
`L²`, `A` is `L²` and `B` is bounded, or `B` is `L²` and `A` is bounded. -/
theorem jai_int3 {μ : Measure Plane} (x A B : Plane → ℝ) (hx : MemLp x 2 μ)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hcase : (MemLp A 2 μ ∧ ∃ M : ℝ, ∀ z, |B z| ≤ M) ∨
      (MemLp B 2 μ ∧ ∃ M : ℝ, ∀ z, |A z| ≤ M)) :
    Integrable (fun z => x z * (A z * B z)) μ := by
  rcases hcase with ⟨hA2, M, hM⟩ | ⟨hB2, M, hM⟩
  · have h1 : Integrable (x * A) μ := hx.integrable_mul hA2
    have h2 : Integrable (fun z => (x * A) z * B z) μ :=
      h1.mul_bdd (c := M) hB (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hM z)
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    try simp only [Pi.mul_apply]
    ring
  · have h1 : Integrable (x * B) μ := hx.integrable_mul hB2
    have h2 : Integrable (fun z => (x * B) z * A z) μ :=
      h1.mul_bdd (c := M) hA (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hM z)
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    try simp only [Pi.mul_apply]
    ring

/-- Leibniz expansion of the `k`-th component of a word derivative of `(u·∇)h`. -/
theorem jai_expand (u h : Plane → Vec) (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    (w : List Bool) (k : Fin 2) (z : Plane) :
    wordComp w (advB u h) k z =
      ((wacSplits w).map (fun p => wordComp p.1 u 0 z * wordComp (p.2 ++ [true]) h k z +
        wordComp p.1 u 1 z * wordComp (p.2 ++ [false]) h k z)).sum := by
  have hF0 : ContDiff ℝ ∞ (fun x => u x 0) := wac_comp_cd hu 0
  have hF1 : ContDiff ℝ ∞ (fun x => u x 1) := wac_comp_cd hu 1
  have hH : ContDiff ℝ ∞ (fun x => h x k) := wac_comp_cd hh k
  have hD0 : ContDiff ℝ ∞ (B0151.derivWord [true] (fun x => h x k)) :=
    B0151.contDiff_derivWord hH [true]
  have hD1 : ContDiff ℝ ∞ (B0151.derivWord [false] (fun x => h x k)) :=
    B0151.contDiff_derivWord hH [false]
  have hP0 : ContDiff ℝ ∞ (fun x => u x 0 * B0151.derivWord [true] (fun y => h y k) x) :=
    hF0.mul hD0
  have hP1 : ContDiff ℝ ∞ (fun x => u x 1 * B0151.derivWord [false] (fun y => h y k) x) :=
    hF1.mul hD1
  have hfun : (fun x => advB u h x k) = fun x =>
      u x 0 * B0151.derivWord [true] (fun y => h y k) x +
        u x 1 * B0151.derivWord [false] (fun y => h y k) x := by
    funext x
    rw [advB_apply]
    simp [advTerm, dirOf, Fin.sum_univ_two, wordComp]
  have a0 : B0151.derivWord w (fun x => u x 0 * B0151.derivWord [true] (fun y => h y k) x) z =
      ((wacSplits w).map (fun p => B0151.derivWord p.1 (fun x => u x 0) z *
        B0151.derivWord (p.2 ++ [true]) (fun y => h y k) z)).sum :=
    wac_gen w (fun x => u x 0) (fun y => h y k) hF0 hH true z
  have a1 : B0151.derivWord w (fun x => u x 1 * B0151.derivWord [false] (fun y => h y k) x) z =
      ((wacSplits w).map (fun p => B0151.derivWord p.1 (fun x => u x 1) z *
        B0151.derivWord (p.2 ++ [false]) (fun y => h y k) z)).sum :=
    wac_gen w (fun x => u x 1) (fun y => h y k) hF1 hH false z
  have e : wordComp w (advB u h) k = B0151.derivWord w (fun x =>
      u x 0 * B0151.derivWord [true] (fun y => h y k) x +
        u x 1 * B0151.derivWord [false] (fun y => h y k) x) := by
    unfold wordComp
    rw [hfun]
  rw [e, ForcingIBP.derivWord_add_smooth w _ _ hP0 hP1]
  dsimp only
  rw [a0, a1, ← wac_sum_map_add]
  rfl

theorem jtAdvInt_proof : UnforcedLeray.Short.PartI.JTAdvInt := by
  intro j c u h f hu hh hf hor hbu hbh
  have hbnd : ∀ (a : List Bool) (m : Fin 2) (b : List Bool) (k : Fin 2),
      (MemLp (wordComp a u m) 2 (Cyl.cellμ c) ∧ ∃ M : ℝ, ∀ z, |wordComp b h k z| ≤ M) ∨
      (MemLp (wordComp b h k) 2 (Cyl.cellμ c) ∧ ∃ M : ℝ, ∀ z, |wordComp a u m z| ≤ M) := by
    intro a m b k
    rcases hor with hUL | hHL
    · exact Or.inl ⟨hUL.2.2 a m, hbh b k⟩
    · exact Or.inr ⟨hHL.2.2 b k, hbu a m⟩
  have hW : ∀ (w : List Bool) (k : Fin 2),
      Integrable (fun z => wordComp w f k z * wordComp w (advB u h) k z) (Cyl.cellμ c) := by
    intro w k
    have hfun : (fun z => wordComp w f k z * wordComp w (advB u h) k z) =
        fun z => ((wacSplits w).map (fun p => wordComp w f k z *
          (wordComp p.1 u 0 z * wordComp (p.2 ++ [true]) h k z +
            wordComp p.1 u 1 z * wordComp (p.2 ++ [false]) h k z))).sum := by
      funext z
      rw [jai_expand u h hu hh w k z, jai_list_mul]
    rw [hfun]
    refine jai_list_integrable (fun p z => wordComp w f k z *
      (wordComp p.1 u 0 z * wordComp (p.2 ++ [true]) h k z +
        wordComp p.1 u 1 z * wordComp (p.2 ++ [false]) h k z)) (wacSplits w) ?_
    intro p _
    have hx : MemLp (wordComp w f k) 2 (Cyl.cellμ c) := hf.2.2 w k
    have k0 := jai_int3 (μ := Cyl.cellμ c) (wordComp w f k)
      (fun z => wordComp p.1 u 0 z) (fun z => wordComp (p.2 ++ [true]) h k z) hx
      (contDiff_wordComp hu p.1 0).continuous.aestronglyMeasurable
      (contDiff_wordComp hh (p.2 ++ [true]) k).continuous.aestronglyMeasurable
      (hbnd p.1 0 (p.2 ++ [true]) k)
    have k1 := jai_int3 (μ := Cyl.cellμ c) (wordComp w f k)
      (fun z => wordComp p.1 u 1 z) (fun z => wordComp (p.2 ++ [false]) h k z) hx
      (contDiff_wordComp hu p.1 1).continuous.aestronglyMeasurable
      (contDiff_wordComp hh (p.2 ++ [false]) k).continuous.aestronglyMeasurable
      (hbnd p.1 1 (p.2 ++ [false]) k)
    refine (k0.add k1).congr (Filter.Eventually.of_forall fun z => ?_)
    try dsimp only
    try simp only [Pi.add_apply]
    ring
  unfold JetInt
  exact integrable_finsetSum _ fun w _ => integrable_finsetSum _ fun k _ => hW w k

end UnforcedLeray.Short.PartI
