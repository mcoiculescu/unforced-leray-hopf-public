import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.AdvInt

/-!
# Part I, task `PartI:T08/7/2/3/2` (`JTBTerm`): one Leibniz term by Cauchy-Schwarz

Source: `the November 2 reference manuscript` lines 352-358.

For one term `∫_cell ∂_w f_k · (∂_a f_m · ∂_{b·dirOf m} V_k)`, the `V`-factor is bounded by
`M_{|b|+1}` (`JTHyp`, `List.length_append`), so `|∫ A·(B·C)| ≤ M · √(∫ B²) · √(∫ A²)` by
`ForcingIBP.abs_int_cs` (Cauchy-Schwarz on the cell) together with `∫ (B·C)² ≤ M² ∫ B²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem jtBTerm_proof : UnforcedLeray.Short.PartI.JTBTerm := by
  intro c V f G M H w p m k
  obtain ⟨-, hV, -, -, hf, -, -, -, hM⟩ := H
  have hfs : ContDiff ℝ ∞ f := hf.1
  have hCb : ∀ z : Plane, |wordComp (p.2 ++ [dirOf m]) V k z| ≤ M (p.2.length + 1) := by
    intro z
    have h := hM (p.2 ++ [dirOf m]) k z
    rwa [List.length_append, List.length_singleton] at h
  set K : ℝ := M (p.2.length + 1) with hKd
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hCb 0)
  have LA : MemLp (wordComp w f k) 2 (Cyl.cellμ c) := hf.2.2 w k
  have LB : MemLp (wordComp p.1 f m) 2 (Cyl.cellμ c) := hf.2.2 p.1 m
  have cB : AEStronglyMeasurable (wordComp p.1 f m) (Cyl.cellμ c) :=
    (contDiff_wordComp hfs p.1 m).continuous.aestronglyMeasurable
  have cC : AEStronglyMeasurable (fun z => wordComp (p.2 ++ [dirOf m]) V k z) (Cyl.cellμ c) :=
    (contDiff_wordComp hV (p.2 ++ [dirOf m]) k).continuous.aestronglyMeasurable
  -- integrability of the product `A · (B · C)`
  have hint : Integrable (fun z => wordComp w f k z *
      (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)) (Cyl.cellμ c) :=
    jai_int3 (μ := Cyl.cellμ c) (wordComp w f k) (fun z => wordComp p.1 f m z)
      (fun z => wordComp (p.2 ++ [dirOf m]) V k z) LA cB cC (Or.inl ⟨LB, K, hCb⟩)
  -- integrability of `B² · C²`, i.e. of `(B · C)²`
  have hbd : ∀ z : Plane, |wordComp (p.2 ++ [dirOf m]) V k z *
      wordComp (p.2 ++ [dirOf m]) V k z| ≤ K * K := fun z => by
    rw [abs_mul]
    exact mul_le_mul (hCb z) (hCb z) (abs_nonneg _) hK0
  have hsq1 : Integrable (fun z => wordComp p.1 f m z *
      (wordComp p.1 f m z * (wordComp (p.2 ++ [dirOf m]) V k z *
        wordComp (p.2 ++ [dirOf m]) V k z))) (Cyl.cellμ c) :=
    jai_int3 (μ := Cyl.cellμ c) (wordComp p.1 f m) (fun z => wordComp p.1 f m z)
      (fun z => wordComp (p.2 ++ [dirOf m]) V k z * wordComp (p.2 ++ [dirOf m]) V k z) LB cB
      (cC.mul cC) (Or.inl ⟨LB, K * K, hbd⟩)
  have hsqBC : Integrable (fun z => (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) *
      (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)) (Cyl.cellμ c) :=
    hsq1.congr (Filter.Eventually.of_forall fun z => by
      try dsimp only
      ring)
  have hsqB : Integrable (fun z => wordComp p.1 f m z * wordComp p.1 f m z) (Cyl.cellμ c) :=
    LB.integrable_mul LB
  have haa : IntegrableOn (fun z => wordComp w f k z * wordComp w f k z) (Cyl.cell c) :=
    LA.integrable_mul LA
  have hab : IntegrableOn (fun z => wordComp w f k z *
      (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)) (Cyl.cell c) := hint
  have hbb : IntegrableOn (fun z => (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) *
      (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)) (Cyl.cell c) := hsqBC
  -- Cauchy-Schwarz on the cell
  have h1 : |∫ z in Cyl.cell c, wordComp w f k z *
        (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)| ≤
      Real.sqrt (∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z) *
        Real.sqrt (∫ z in Cyl.cell c, (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) *
          (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)) :=
    ForcingIBP.abs_int_cs (c := c) (wordComp w f k)
      (fun z => wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) haa hbb hab
  -- the square of the product is bounded by `K²` times the square of the `f`-factor
  have hsq : ∫ z in Cyl.cell c, (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) *
      (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) ≤
      (K * K) * ∫ z in Cyl.cell c, wordComp p.1 f m z * wordComp p.1 f m z := by
    rw [← integral_const_mul]
    refine integral_mono hsqBC (hsqB.const_mul _) fun z => ?_
    have hs : wordComp (p.2 ++ [dirOf m]) V k z * wordComp (p.2 ++ [dirOf m]) V k z ≤ K * K := by
      rw [← abs_mul_abs_self]
      exact mul_self_le_mul_self (abs_nonneg _) (hCb z)
    have e2 : (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) *
        (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) =
        (wordComp (p.2 ++ [dirOf m]) V k z * wordComp (p.2 ++ [dirOf m]) V k z) *
          (wordComp p.1 f m z * wordComp p.1 f m z) := by ring
    show (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) *
        (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) ≤
        (K * K) * (wordComp p.1 f m z * wordComp p.1 f m z)
    rw [e2]
    exact mul_le_mul_of_nonneg_right hs (mul_self_nonneg _)
  have h3 : Real.sqrt (∫ z in Cyl.cell c, (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z) *
      (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)) ≤
      K * Real.sqrt (∫ z in Cyl.cell c, wordComp p.1 f m z * wordComp p.1 f m z) := by
    refine (Real.sqrt_le_sqrt hsq).trans ?_
    rw [Real.sqrt_mul (mul_self_nonneg K), Real.sqrt_mul_self hK0]
  have h4 := h1.trans (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _))
  refine h4.trans (le_of_eq ?_)
  ring

end UnforcedLeray.Short.PartI
