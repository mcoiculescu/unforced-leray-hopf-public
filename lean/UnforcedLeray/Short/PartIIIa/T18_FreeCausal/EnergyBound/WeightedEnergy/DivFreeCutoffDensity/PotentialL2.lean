import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QL2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.PotentialFormulas

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/7`: `L²` bounds for the stream potential

Target (`Sub/T18_3_1_1.lean`): `DfcPotentialL2`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552 (density of divergence-free
fields; the stream potential `θ = dfcPotential c φ` of an `H¹` divergence-free test field).

Mathematics. Put `f₁ = φ·1`, `P = dfcQPrim c f₁` (continuous, in `L²(cell)` by `dfcQL2`) and
`Q = dfcQInt c P` (in `L²(ℝ)` by `dfcQL2`). Then `dfcPotential c φ x = -P x + c⁻¹ Q(x.2)`.
The function `(q, η) ↦ g(η)` of an `L²(ℝ)` function `g` lies in `L²(cell)` because the cell
integral of its square is `c ∫ g²` (`ql2_cell_prod`). Hence `θ ∈ L²(cell)`.
For `∂_η θ`, use `dfcPotentialFormulas`: `∂_η θ = φ₀ - c⁻¹ Q₀(η)` with `Q₀ = dfcQInt c (φ·0)`,
which is in `L²(cell)` as `φ₀ ∈ L²(cell)` and `Q₀ ∈ L²(ℝ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DfcPotentialL2Aux

/-- A continuous `L²(ℝ)` function of `η` is, as a function of `(q, η)`, in `L²(cell)`. -/
theorem sndMemLp {c : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (hL : MemLp g 2 volume) :
    MemLp (fun x : ℝ × ℝ => g x.2) 2 (volume.restrict (B0579.cell c)) := by
  have hcont : Continuous (fun x : ℝ × ℝ => g x.2) := hg.comp continuous_snd
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine ⟨(hcont.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)]
  have hG : Measurable (fun x : ℝ × ℝ => ENNReal.ofReal (g x.2 ^ 2)) :=
    (ENNReal.continuous_ofReal.comp ((hg.comp continuous_snd).pow 2)).measurable
  have hK : ∫⁻ η, ENNReal.ofReal (g η ^ 2) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mp
      hL.integrable_sq.hasFiniteIntegral
  have e := ql2_cell_prod (c := c) (fun x : ℝ × ℝ => ENNReal.ofReal (g x.2 ^ 2)) hG
  have hlen : c / 2 - -(c / 2) = c := by ring
  calc ∫⁻ x in B0579.cell c, ENNReal.ofReal (g x.2 ^ 2)
      = ∫⁻ q in Ico (-(c / 2)) (c / 2), ∫⁻ η, ENNReal.ofReal (g η ^ 2) := e
    _ = ENNReal.ofReal c * ∫⁻ η, ENNReal.ofReal (g η ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ico, hlen, mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK

end DfcPotentialL2Aux

/-- **Target** `PartIII-a:T18/3/1/1/7`: the stream potential and its `η`-derivative are in
`L²(cell)`. -/
theorem dfcPotentialL2 : UnforcedLeray.Short.IIIa.DfcPotentialL2 := by
  unfold UnforcedLeray.Short.IIIa.DfcPotentialL2
  intro c hc φ hφ hM
  have hf1 : Continuous (fun x : ℝ × ℝ => φ x 1) := (hφ.smooth 1).continuous
  have hf0 : Continuous (fun x : ℝ × ℝ => φ x 0) := (hφ.smooth 0).continuous
  have hPc : Continuous (dfcQPrim c (fun y => φ y 1)) := ql2_cont_P hf1
  have hPL : MemLp (dfcQPrim c (fun y => φ y 1)) 2 (volume.restrict (B0579.cell c)) :=
    (dfcQL2 c hc _ hf1 (hφ.l2 1)).2
  have hQc : Continuous (dfcQInt c (dfcQPrim c (fun y => φ y 1))) := ql2_cont_Q hPc
  have hQL : MemLp (dfcQInt c (dfcQPrim c (fun y => φ y 1))) 2 volume :=
    (dfcQL2 c hc _ hPc hPL).1
  constructor
  · have h := hPL.neg.add ((DfcPotentialL2Aux.sndMemLp (c := c) hQc hQL).const_mul c⁻¹)
    exact h
  · have hform := dfcPotentialFormulas c hc φ hφ hM
    have e : (fun x => B0579.pd 1 (dfcPotential c φ) x)
        = fun x => φ x 0 - c⁻¹ * dfcQInt c (fun y => φ y 0) x.2 :=
      funext fun x => hform.2.2.2 x
    rw [e]
    have hQ0c : Continuous (dfcQInt c (fun y => φ y 0)) := ql2_cont_Q hf0
    have hQ0 : MemLp (dfcQInt c (fun y => φ y 0)) 2 volume :=
      (dfcQL2 c hc _ hf0 (hφ.l2 0)).1
    exact (hφ.l2 0).sub ((DfcPotentialL2Aux.sndMemLp (c := c) hQ0c hQ0).const_mul c⁻¹)

end UnforcedLeray.Short.IIIa
