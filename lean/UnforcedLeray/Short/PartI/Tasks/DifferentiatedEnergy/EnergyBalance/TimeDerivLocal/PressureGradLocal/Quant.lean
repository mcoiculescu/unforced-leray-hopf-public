import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_6
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.PressureGradJetL2OfDivForm
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Units.B0151.Linf

/-!
# Part I, task `PartI:T08/4/1/1/6/4` (`pressureGradJetL2Quant_proof_of`): word-induction for the
quantitative pressure-gradient estimate

Source of record: `the November 2 reference manuscript` lines 266-270, 326-329.
The Prop is `PressureGradJetL2Quant` in `Sub/PartI_T08_4_1_1_6.lean`.

Route. Induction on the word `w`. Nil: `h0` with `L = {[]}`, `C = 4`. Cons `b :: w`: the pointwise
bound `(∂_b h_k)² ≤ (∂_q h_k)² + (∂_η h_k)²` with `h_k = ∂_w ∂_k π`, then `h1` for `h_k`, the
induction hypothesis for `∫ ∑_k h_k²`, and `h2` with `(Δ h_k)² ≤ 2 (∂ F)² + 2 (∂ F)²`.
The qualitative `MemLp` of word jets of `∇π` comes from `pressureGradJetL2OfDivForm_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Word jets of `∇π` are smooth and periodic when `π` is smooth and periodic. -/
theorem pgq_gradS_word_props {c : ℝ} {π : Plane → ℝ} (hπ : ContDiff ℝ ∞ π)
    (hper : Cyl.IsPeriodic c π) (w : List Bool) (k : Fin 2) :
    ContDiff ℝ ∞ (wordComp w (Train.gradS π) k) ∧
      Cyl.IsPeriodic c (wordComp w (Train.gradS π) k) := by
  constructor
  · refine B0151.contDiff_derivWord ?_ w
    fin_cases k
    · exact ForcingIBP.cd_partialQ hπ
    · exact ForcingIBP.cd_partialEta hπ
  · have h0 : B0151.IsPeriodicQ c π := fun q η => hper (q, η)
    have key : B0151.IsPeriodicQ c (fun x => Train.gradS π x k) := by
      fin_cases k
      · exact h0.partialX
      · exact h0.partialY
    intro z
    exact B0151.periodic_derivWord key w z.1 z.2

/-- One word step, pointwise: `(∂_b g)² ≤ (∂_q g)² + (∂_η g)²`. -/
theorem pgq_wordStep_sq (b : Bool) (w : List Bool) (f : Plane → Vec) (k : Fin 2) (z : Plane) :
    (wordComp (b :: w) f k z) ^ 2 ≤
      (Cyl.partialQ (wordComp w f k) z) ^ 2 + (Cyl.partialEta (wordComp w f k) z) ^ 2 := by
  cases b with
  | true =>
    have e : wordComp (true :: w) f k z = Cyl.partialQ (wordComp w f k) z := rfl
    rw [e]
    nlinarith [sq_nonneg (Cyl.partialEta (wordComp w f k) z)]
  | false =>
    have e : wordComp (false :: w) f k z = Cyl.partialEta (wordComp w f k) z := rfl
    rw [e]
    nlinarith [sq_nonneg (Cyl.partialQ (wordComp w f k) z)]

/-- The finite-set sum is monotone in the set. -/
theorem pgq_sumL_mono (c : ℝ) (F : Plane → Vec) (L L' : Finset (List Bool)) (hsub : L ⊆ L') :
    ∑ u ∈ L, ∑ m : Fin 2, ∫ z in Cyl.cell c, (wordComp u F m z) ^ 2 ≤
      ∑ u ∈ L', ∑ m : Fin 2, ∫ z in Cyl.cell c, (wordComp u F m z) ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun u _ _ => Finset.sum_nonneg (fun m _ => integral_nonneg (fun z => sq_nonneg _)))

/-- A single term is bounded by the full finite-set sum. -/
theorem pgq_term_le (c : ℝ) (F : Plane → Vec) (L' : Finset (List Bool)) (u : List Bool)
    (hu : u ∈ L') (m : Fin 2) :
    ∫ z in Cyl.cell c, (wordComp u F m z) ^ 2 ≤
      ∑ u' ∈ L', ∑ m' : Fin 2, ∫ z in Cyl.cell c, (wordComp u' F m' z) ^ 2 := by
  have hnn : ∀ u' : List Bool, 0 ≤ ∑ m' : Fin 2, ∫ z in Cyl.cell c, (wordComp u' F m' z) ^ 2 :=
    fun u' => Finset.sum_nonneg (fun m' _ => integral_nonneg (fun z => sq_nonneg _))
  calc ∫ z in Cyl.cell c, (wordComp u F m z) ^ 2
      ≤ ∑ m' : Fin 2, ∫ z in Cyl.cell c, (wordComp u F m' z) ^ 2 :=
        Finset.single_le_sum (f := fun m' : Fin 2 => ∫ z in Cyl.cell c, (wordComp u F m' z) ^ 2)
          (fun m' _ => integral_nonneg (fun z => sq_nonneg _)) (Finset.mem_univ m)
    _ ≤ ∑ u' ∈ L', ∑ m' : Fin 2, ∫ z in Cyl.cell c, (wordComp u' F m' z) ^ 2 :=
        Finset.single_le_sum
          (f := fun u' : List Bool => ∑ m' : Fin 2, ∫ z in Cyl.cell c, (wordComp u' F m' z) ^ 2)
          (fun u' _ => hnn u') hu

theorem pressureGradJetL2Quant_proof_of (h0 : UnforcedLeray.Short.PartI.PressureGradOrder0Quant)
    (h1 : UnforcedLeray.Short.PartI.GradL2QuantP)
    (h2 : UnforcedLeray.Short.PartI.PressureGradWordLapId) :
    UnforcedLeray.Short.PartI.PressureGradJetL2Quant := by
  choose U0 U1 hU using h2
  intro w
  induction w with
  | nil =>
    refine ⟨{[]}, 4, by norm_num, ?_⟩
    intro c hc π F hπ hper hbd hF hFper hlap
    have e : ∀ (G : Plane → Vec) (m : Fin 2) (z : Plane), wordComp [] G m z = G z m :=
      fun _ _ _ => rfl
    simp only [e, Finset.sum_singleton]
    exact h0 c hc π F hπ hper hbd hF hFper hlap
  | cons b w ih =>
    obtain ⟨L, C, hC0, hIH⟩ := ih
    obtain ⟨L', hL'⟩ : ∃ L' : Finset (List Bool),
        L' = L ∪ Finset.univ.image (fun k : Fin 2 => U0 w k)
          ∪ Finset.univ.image (fun k : Fin 2 => U1 w k) := ⟨_, rfl⟩
    have hsub : L ⊆ L' := by
      rw [hL']
      exact fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    have mem0 : ∀ k : Fin 2, U0 w k ∈ L' := fun k => by
      rw [hL']
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
    have mem1 : ∀ k : Fin 2, U1 w k ∈ L' := fun k => by
      rw [hL']
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    refine ⟨L', 2 * C + 16, by linarith, ?_⟩
    intro c hc π F hπ hper hbd hF hFper hlap
    have hF' : ContDiff ℝ ∞ F ∧
        ∀ (u : List Bool) (k : Fin 2), MemLp (wordComp u F k) 2 (Cyl.cellμ c) := hF
    obtain ⟨hFsm, hFL2⟩ := hF'
    have hqual : ∀ (u : List Bool) (k : Fin 2),
        MemLp (wordComp u (Train.gradS π) k) 2 (Cyl.cellμ c) :=
      fun u k => pressureGradJetL2OfDivForm_proof c hc π F hπ hper hbd hF hFper hlap u k
    have hL : ∀ k : Fin 2, Train.lapS (wordComp w (Train.gradS π) k) =
        fun z => -(wordComp (U0 w k) F 0 z + wordComp (U1 w k) F 1 z) := by
      intro k
      funext z
      exact hU w k π F hπ hFsm hlap z
    have hLM : ∀ k : Fin 2, MemLp (Train.lapS (wordComp w (Train.gradS π) k)) 2
        (Cyl.cellμ c) := by
      intro k
      rw [hL k]
      exact ((hFL2 (U0 w k) 0).add (hFL2 (U1 w k) 1)).neg
    have hLsq : ∀ k : Fin 2,
        ∫ z in Cyl.cell c, (Train.lapS (wordComp w (Train.gradS π) k) z) ^ 2 ≤
          2 * (∫ z in Cyl.cell c, (wordComp (U0 w k) F 0 z) ^ 2) +
            2 * (∫ z in Cyl.cell c, (wordComp (U1 w k) F 1 z) ^ 2) := by
      intro k
      have ia : Integrable (fun z => (wordComp (U0 w k) F 0 z) ^ 2) (volume.restrict (Cyl.cell c)) :=
        (hFL2 (U0 w k) 0).integrable_sq
      have ib : Integrable (fun z => (wordComp (U1 w k) F 1 z) ^ 2) (volume.restrict (Cyl.cell c)) :=
        (hFL2 (U1 w k) 1).integrable_sq
      have hpt : ∀ z, (Train.lapS (wordComp w (Train.gradS π) k) z) ^ 2 ≤
          2 * (wordComp (U0 w k) F 0 z) ^ 2 + 2 * (wordComp (U1 w k) F 1 z) ^ 2 := by
        intro z
        have hz : Train.lapS (wordComp w (Train.gradS π) k) z =
            -(wordComp (U0 w k) F 0 z + wordComp (U1 w k) F 1 z) :=
          congrFun (hL k) z
        rw [hz]
        nlinarith [sq_nonneg (wordComp (U0 w k) F 0 z - wordComp (U1 w k) F 1 z)]
      calc ∫ z in Cyl.cell c, (Train.lapS (wordComp w (Train.gradS π) k) z) ^ 2
          ≤ ∫ z in Cyl.cell c, (2 * (wordComp (U0 w k) F 0 z) ^ 2 +
              2 * (wordComp (U1 w k) F 1 z) ^ 2) :=
            integral_mono (hLM k).integrable_sq ((ia.const_mul 2).add (ib.const_mul 2)) hpt
        _ = 2 * (∫ z in Cyl.cell c, (wordComp (U0 w k) F 0 z) ^ 2) +
              2 * (∫ z in Cyl.cell c, (wordComp (U1 w k) F 1 z) ^ 2) := by
            rw [integral_add (ia.const_mul 2) (ib.const_mul 2), integral_const_mul,
              integral_const_mul]
    have hK : ∀ k : Fin 2,
        ∫ z in Cyl.cell c, (wordComp (b :: w) (Train.gradS π) k z) ^ 2 ≤
          ∫ z in Cyl.cell c, ((Cyl.partialQ (wordComp w (Train.gradS π) k) z) ^ 2 +
            (Cyl.partialEta (wordComp w (Train.gradS π) k) z) ^ 2) := by
      intro k
      have hJ : Integrable (fun z => (Cyl.partialQ (wordComp w (Train.gradS π) k) z) ^ 2 +
          (Cyl.partialEta (wordComp w (Train.gradS π) k) z) ^ 2) (Cyl.cellμ c) :=
        (hqual (true :: w) k).integrable_sq.add (hqual (false :: w) k).integrable_sq
      exact integral_mono (hqual (b :: w) k).integrable_sq hJ
        (fun z => pgq_wordStep_sq b w (Train.gradS π) k z)
    have hG : ∀ k : Fin 2,
        ∫ z in Cyl.cell c, ((Cyl.partialQ (wordComp w (Train.gradS π) k) z) ^ 2 +
            (Cyl.partialEta (wordComp w (Train.gradS π) k) z) ^ 2) ≤
          2 * ((∫ z in Cyl.cell c, (wordComp w (Train.gradS π) k z) ^ 2) +
            ∫ z in Cyl.cell c, (Train.lapS (wordComp w (Train.gradS π) k) z) ^ 2) := by
      intro k
      exact h1 c (wordComp w (Train.gradS π) k) hc (pgq_gradS_word_props hπ hper w k).1
        (pgq_gradS_word_props hπ hper w k).2 (hqual w k) (hLM k)
    have int0 : Integrable (fun z => (wordComp w (Train.gradS π) 0 z) ^ 2) (Cyl.cellμ c) :=
      (hqual w 0).integrable_sq
    have int1 : Integrable (fun z => (wordComp w (Train.gradS π) 1 z) ^ 2) (Cyl.cellμ c) :=
      (hqual w 1).integrable_sq
    have hsum : ∫ z in Cyl.cell c, ∑ k : Fin 2, (wordComp w (Train.gradS π) k z) ^ 2 =
        (∫ z in Cyl.cell c, (wordComp w (Train.gradS π) 0 z) ^ 2) +
          ∫ z in Cyl.cell c, (wordComp w (Train.gradS π) 1 z) ^ 2 := by
      simp only [Fin.sum_univ_two]
      exact integral_add int0 int1
    have hsumB : ∫ z in Cyl.cell c, ∑ k : Fin 2, (wordComp (b :: w) (Train.gradS π) k z) ^ 2 =
        (∫ z in Cyl.cell c, (wordComp (b :: w) (Train.gradS π) 0 z) ^ 2) +
          ∫ z in Cyl.cell c, (wordComp (b :: w) (Train.gradS π) 1 z) ^ 2 := by
      simp only [Fin.sum_univ_two]
      exact integral_add (hqual (b :: w) 0).integrable_sq (hqual (b :: w) 1).integrable_sq
    have hIHv := hIH c hc π F hπ hper hbd hF hFper hlap
    rw [hsum] at hIHv
    have hSL := pgq_sumL_mono c F L L' hsub
    have hCS := mul_le_mul_of_nonneg_left hSL hC0
    have hA0 := pgq_term_le c F L' (U0 w 0) (mem0 0) 0
    have hA1 := pgq_term_le c F L' (U0 w 1) (mem0 1) 0
    have hB0 := pgq_term_le c F L' (U1 w 0) (mem1 0) 1
    have hB1 := pgq_term_le c F L' (U1 w 1) (mem1 1) 1
    rw [hsumB]
    have K0 := hK 0
    have K1 := hK 1
    have G0 := hG 0
    have G1 := hG 1
    have S0 := hLsq 0
    have S1 := hLsq 1
    linarith
  
end UnforcedLeray.Short.PartI
