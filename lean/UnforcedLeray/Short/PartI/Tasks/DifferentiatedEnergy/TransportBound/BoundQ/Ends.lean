import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundA

/-!
# Part I, task `PartI:T08/7/3/1/2`: `JTQEnds` (commutator terms at the ends)

Source: `the November 2 reference manuscript` lines 352-358.
For `|a| = 1` or `|a| = j`, one factor of the triple is bounded by `G` and the other two are
word components of length `j`; Cauchy-Schwarz (`ForcingIBP.abs_int_cs`) with `C = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Cauchy-Schwarz for one term `∫ F (B K)` with `|B| ≤ G`, `F`, `K` word components of length
`j`. -/
theorem ends_core {c : ℝ} {f : Plane → Vec} (hf : CellSmoothL2 c f) {j : ℕ} {G : ℝ}
    (hG0 : 0 ≤ G) (u v : List Bool) (k₁ k₂ : Fin 2) (hu : u.length = j) (hv : v.length = j)
    (B : Plane → ℝ) (hB : ∀ z, |B z| ≤ G) (hBc : AEStronglyMeasurable B (Cyl.cellμ c)) :
    |∫ z in Cyl.cell c, wordComp u f k₁ z * (B z * wordComp v f k₂ z)| ≤
      G * jetEnergy c j f := by
  have hF2 : MemLp (wordComp u f k₁) 2 (Cyl.cellμ c) := hf.2.2 u k₁
  have hK2 : MemLp (wordComp v f k₂) 2 (Cyl.cellμ c) := hf.2.2 v k₂
  have hJ0 : 0 ≤ jetEnergy c j f := jetEnergy_nonneg c j f
  have hFJ : ∫ z in Cyl.cell c, wordComp u f k₁ z * wordComp u f k₁ z ≤ jetEnergy c j f := by
    have := ba_single_le hf u k₁
    rwa [hu] at this
  have hKJ : ∫ z in Cyl.cell c, wordComp v f k₂ z * wordComp v f k₂ z ≤ jetEnergy c j f := by
    have := ba_single_le hf v k₂
    rwa [hv] at this
  have hPP : Integrable (fun z => (B z * wordComp u f k₁ z) * (B z * wordComp u f k₁ z))
      (Cyl.cellμ c) :=
    (ba_int3 (μ := Cyl.cellμ c) (x := wordComp u f k₁) (y := wordComp u f k₁)
      (B := fun z => B z * B z) hF2 hF2 (hBc.mul hBc) (G * G)
      (fun z => by
        rw [abs_mul]
        exact mul_le_mul (hB z) (hB z) (abs_nonneg _) hG0)).congr
      (Filter.Eventually.of_forall fun z => by dsimp only; ring)
  have hPK : Integrable (fun z => (B z * wordComp u f k₁ z) * wordComp v f k₂ z)
      (Cyl.cellμ c) :=
    (ba_int3 (μ := Cyl.cellμ c) (x := wordComp u f k₁) (y := wordComp v f k₂)
      hF2 hK2 hBc G hB).congr (Filter.Eventually.of_forall fun z => by dsimp only; ring)
  have hKK : Integrable (fun z => wordComp v f k₂ z * wordComp v f k₂ z) (Cyl.cellμ c) :=
    hK2.integrable_mul hK2
  have hFF : Integrable (fun z => wordComp u f k₁ z * wordComp u f k₁ z) (Cyl.cellμ c) :=
    hF2.integrable_mul hF2
  have hcs := ForcingIBP.abs_int_cs (c := c) (fun z => B z * wordComp u f k₁ z)
    (wordComp v f k₂) hPP hKK hPK
  have hrw : ∫ z in Cyl.cell c, wordComp u f k₁ z * (B z * wordComp v f k₂ z) =
      ∫ z in Cyl.cell c, (B z * wordComp u f k₁ z) * wordComp v f k₂ z :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by dsimp only; ring)
  rw [hrw]
  refine le_trans hcs ?_
  have hP : ∫ z in Cyl.cell c, (B z * wordComp u f k₁ z) * (B z * wordComp u f k₁ z) ≤
      G * G * jetEnergy c j f := by
    calc ∫ z in Cyl.cell c, (B z * wordComp u f k₁ z) * (B z * wordComp u f k₁ z)
        ≤ ∫ z in Cyl.cell c, (G * G) * (wordComp u f k₁ z * wordComp u f k₁ z) := by
          refine integral_mono hPP (hFF.const_mul (G * G)) fun z => ?_
          have h2 : B z * B z ≤ G * G := by
            rw [← abs_mul_abs_self (B z)]
            exact mul_le_mul (hB z) (hB z) (abs_nonneg _) hG0
          calc (B z * wordComp u f k₁ z) * (B z * wordComp u f k₁ z)
              = (B z * B z) * (wordComp u f k₁ z * wordComp u f k₁ z) := by ring
            _ ≤ (G * G) * (wordComp u f k₁ z * wordComp u f k₁ z) :=
              mul_le_mul_of_nonneg_right h2 (mul_self_nonneg _)
      _ = G * G * ∫ z in Cyl.cell c, wordComp u f k₁ z * wordComp u f k₁ z := by
          rw [integral_const_mul]
      _ ≤ G * G * jetEnergy c j f := mul_le_mul_of_nonneg_left hFJ (mul_nonneg hG0 hG0)
  have hsq1 : Real.sqrt (∫ z in Cyl.cell c, (B z * wordComp u f k₁ z) *
      (B z * wordComp u f k₁ z)) ≤ G * Real.sqrt (jetEnergy c j f) := by
    calc Real.sqrt (∫ z in Cyl.cell c, (B z * wordComp u f k₁ z) *
          (B z * wordComp u f k₁ z))
        ≤ Real.sqrt (G * G * jetEnergy c j f) := Real.sqrt_le_sqrt hP
      _ = G * Real.sqrt (jetEnergy c j f) := by
          rw [Real.sqrt_mul (mul_self_nonneg G), Real.sqrt_mul_self hG0]
  have hsq2 : Real.sqrt (∫ z in Cyl.cell c, wordComp v f k₂ z * wordComp v f k₂ z) ≤
      Real.sqrt (jetEnergy c j f) := Real.sqrt_le_sqrt hKJ
  calc Real.sqrt (∫ z in Cyl.cell c, (B z * wordComp u f k₁ z) *
          (B z * wordComp u f k₁ z)) *
        Real.sqrt (∫ z in Cyl.cell c, wordComp v f k₂ z * wordComp v f k₂ z)
      ≤ (G * Real.sqrt (jetEnergy c j f)) * Real.sqrt (jetEnergy c j f) :=
        mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg _) (mul_nonneg hG0 (Real.sqrt_nonneg _))
    _ = G * jetEnergy c j f := by rw [mul_assoc, Real.mul_self_sqrt hJ0]

theorem jtQEnds_proof : UnforcedLeray.Short.PartI.JTQEnds := by
  intro j
  refine ⟨1, zero_le_one, ?_⟩
  intro c V f G M H w hw p hp hp0 hcase m k
  obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hGb, hMb⟩ := H
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hGb true 0 (0, 0))
  have hwl : w.length = j := mem_wordsOfLength_length hw
  have hlen := wac_splits_len_sum w p hp
  rw [hwl] at hlen
  rw [one_mul]
  rcases hcase with h1 | h1
  · obtain ⟨β, hβ⟩ := List.length_eq_one_iff.mp h1
    rw [hβ] at hlen ⊢
    have hv : (p.2 ++ [dirOf m]).length = j := by
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen ⊢
      omega
    exact ends_core hf hG0 w (p.2 ++ [dirOf m]) k k hwl hv (fun z => wordComp [β] f m z)
      (fun z => hGb β m z) (contDiff_wordComp hf.1 [β] m).continuous.aestronglyMeasurable
  · have hp2 : p.2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hp2, List.nil_append]
    have hrw : ∫ z in Cyl.cell c, wordComp w f k z *
        (wordComp p.1 f m z * wordComp [dirOf m] f k z) =
        ∫ z in Cyl.cell c, wordComp w f k z *
          (wordComp [dirOf m] f k z * wordComp p.1 f m z) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by dsimp only; ring)
    rw [hrw]
    exact ends_core hf hG0 w p.1 k m hwl h1 (fun z => wordComp [dirOf m] f k z)
      (fun z => hGb (dirOf m) k z) (contDiff_wordComp hf.1 [dirOf m] k).continuous.aestronglyMeasurable

end UnforcedLeray.Short.PartI
