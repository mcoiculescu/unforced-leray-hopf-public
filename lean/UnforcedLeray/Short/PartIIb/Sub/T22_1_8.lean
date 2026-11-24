import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont

/-!
# `PartII-b:T22/1/8` (`HeatEqn`) reduced to two kernel-calculus leaves

Source: `the November 2 reference manuscript` lines 2074-2093 (cylinder equation) and
2103-2105 (smoothing); the statements are standard heat-kernel calculus.

* `HeatTimeDeriv` : `d/db (K_b * g)(x) = ∫ (Δ K_a)(x - y) g(y) dy` at `b = a > 0`.
* `HeatLapTransfer` : `K_a * Δg = (ΔK_a) * g` (two integrations by parts).
`heatEqn_of` derives `HeatEqn` from them and the proved `HeatCont`
(right derivative at `0` by `hasDerivWithinAt_Ici_of_tendsto_deriv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

/-- Time derivative of the heat semigroup under the integral sign:
`∂_b (K_b * g)(x) |_{b=a} = ∫ (Δ_z K_a)(x - y) g(y) dy` for `a > 0`, `g` continuous with
`|g| cosh η ≤ B` (uses `∂_b K_b = Δ K_b` pointwise and a locally uniform Gaussian majorant of
`sup_{b ∈ [a/2, 2a]} |∂_b K_b|(x - y)` against `B / cosh y₂`). -/
def HeatTimeDeriv : Prop := ∀ (B : ℝ) (g : Pl → ℝ), Continuous g → WB B g →
  ∀ (a : ℝ), 0 < a → ∀ x : Pl,
    HasDerivAt (fun b => heatSG b g x) (∫ y : Pl, lapP (heatK a) (x - y) * g y) a

/-- Transfer of the Laplacian onto the kernel: for `g ∈ C²` with `g, ∇g, ∇²g` weighted-bounded and
`a > 0`, `K_a * Δg = (ΔK_a) * g` (integrate by parts twice; no boundary terms by the decay of `g`
and of `K_a`, e.g. via `HeatCommute` and `HeatGradFormula`). -/
def HeatLapTransfer : Prop := ∀ (B : ℝ) (g : Pl → ℝ), ContDiff ℝ 2 g → WB B g →
  (∀ j : Fin 2, WB B (B0579.pd j g)) → (∀ i j : Fin 2, WB B (B0579.pd i (B0579.pd j g))) →
  ∀ (a : ℝ), 0 < a → ∀ x : Pl,
    heatSG a (lapP g) x = ∫ y : Pl, lapP (heatK a) (x - y) * g y

lemma pd_contDiff_one {g : Pl → ℝ} (hg : ContDiff ℝ 2 g) (j : Fin 2) :
    ContDiff ℝ 1 (B0579.pd j g) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

lemma lapP_continuous {g : Pl → ℝ} (hg : ContDiff ℝ 2 g) : Continuous (lapP g) := by
  have h : ∀ j : Fin 2, Continuous (B0579.pd j (B0579.pd j g)) := by
    intro j
    have h1 : ContDiff ℝ 0 (fderiv ℝ (B0579.pd j g)) :=
      (pd_contDiff_one hg j).fderiv_right (m := 0) (by norm_num)
    exact h1.continuous.clm_apply continuous_const
  exact (h 0).add (h 1)

lemma lapP_WB {B : ℝ} {g : Pl → ℝ}
    (h : ∀ i j : Fin 2, WB B (B0579.pd i (B0579.pd j g))) : WB (B + B) (lapP g) := by
  intro x
  have h0 := h 0 0 x
  have h1 := h 1 1 x
  unfold lapP
  have hc : 0 < Real.cosh x.2 := Real.cosh_pos _
  calc |B0579.pd 0 (B0579.pd 0 g) x + B0579.pd 1 (B0579.pd 1 g) x| * Real.cosh x.2
      ≤ (|B0579.pd 0 (B0579.pd 0 g) x| + |B0579.pd 1 (B0579.pd 1 g) x|) * Real.cosh x.2 :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) hc.le
    _ ≤ B + B := by nlinarith

theorem heatEqn_of (hT : HeatTimeDeriv) (hL : HeatLapTransfer) (hC : HeatCont) : HeatEqn := by
  intro B g hg2 hW hW1 hW2 x
  have hpos : ∀ a : ℝ, 0 < a → HasDerivAt (fun b => heatSG b g x) (heatSG a (lapP g) x) a := by
    intro a ha
    have := hT B g hg2.continuous hW a ha x
    rwa [← hL B g hg2 hW hW1 hW2 a ha x] at this
  refine ⟨hpos, ?_⟩
  have hcl := hC (B + B) (lapP g) (lapP_continuous hg2) (lapP_WB hW2)
  have hcg := hC B g hg2.continuous hW
  have hderiv : ∀ b ∈ Ioi (0 : ℝ), deriv (fun b => heatSG b g x) b = heatSG b (lapP g) x :=
    fun b hb => (hpos b hb).deriv
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
  · intro b hb
    exact (hpos b hb).differentiableAt.differentiableWithinAt
  · have h1 : ContinuousWithinAt (fun b : ℝ => ((b, x) : ℝ × Pl)) (Ici 0) 0 :=
      (continuous_id.prodMk continuous_const).continuousWithinAt
    have h2 := ContinuousWithinAt.comp (x := (0:ℝ)) (hcg (0, x) (Set.mk_mem_prod (Set.mem_Ici.2 le_rfl) (Set.mem_univ x))) h1 (fun b hb => Set.mk_mem_prod hb (Set.mem_univ x))
    exact (h2.mono Ioi_subset_Ici_self)
  · have h1 : ContinuousWithinAt (fun b : ℝ => ((b, x) : ℝ × Pl)) (Ici 0) 0 :=
      (continuous_id.prodMk continuous_const).continuousWithinAt
    have h2 := ContinuousWithinAt.comp (x := (0:ℝ)) (hcl (0, x) (Set.mk_mem_prod (Set.mem_Ici.2 le_rfl) (Set.mem_univ x))) h1 (fun b hb => Set.mk_mem_prod hb (Set.mem_univ x))
    have h3 : Tendsto (fun b : ℝ => heatSG b (lapP g) x) (𝓝[>] 0) (𝓝 (lapP g x)) := by
      have := (h2.mono Ioi_subset_Ici_self).tendsto
      simpa [Function.comp_def, heatSG] using this
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (hderiv b hb).symm

end UnforcedLeray.Short.IIb.CylPDE
