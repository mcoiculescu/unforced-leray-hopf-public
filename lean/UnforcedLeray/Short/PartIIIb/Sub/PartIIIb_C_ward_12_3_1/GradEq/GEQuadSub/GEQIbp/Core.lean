import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp.Lemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.WeakMulRule

/-!
# `GEQIbp` core: two weak integrations by parts (source 2525-2533)

Abstract form of `GEQIbp`: for weak first derivatives `D` of `U` and weak second derivatives
`DD` (both locally `L²`/`L^{q₀}`), `⟨(u·∇)∂_jΦ, u⟩ = -⟨Φ, F⟩` with the field `F` of
`GEQuadField`.  Proof: `WeakMulRule` for `u_k u_i` (direction `k`), then for the resulting
products (direction `j`), with the test `∂_jΦ_i` moved onto `Φ_i`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF advT phaseInt phaseCell)

theorem q0E_two_le : (2 : ENNReal) ≤ UnforcedLeray.B0412.q0E := by
  unfold UnforcedLeray.B0412.q0E
  rw [UnforcedLeray.B0281.q0_eq, show (2 : ENNReal) = ENNReal.ofReal 2 by simp]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem two_le_two_mul_q0E : (2 : ENNReal) ≤ 2 * UnforcedLeray.B0412.q0E :=
  le_mul_of_one_le_right zero_le (le_trans one_le_two q0E_two_le)

theorem q0E_le_two_mul_q0E : UnforcedLeray.B0412.q0E ≤ 2 * UnforcedLeray.B0412.q0E :=
  le_mul_of_one_le_left zero_le one_le_two

theorem gEQIbp_core {P : ℝ} [Fact (0 < P)]
    (U : Fin 3 → ℝ × UnforcedLeray.Space → ℂ)
    (D : Fin 3 → Fin 3 → ℝ × UnforcedLeray.Space → ℂ)
    (DD : Fin 3 → Fin 3 → Fin 3 → ℝ × UnforcedLeray.Space → ℂ)
    (hU2 : ∀ i, MemLpLoc P (U i) (2 * UnforcedLeray.B0412.q0E))
    (hD2 : ∀ a b, MemLpLoc P (D a b) (2 * UnforcedLeray.B0412.q0E))
    (hDD2 : ∀ a b c, MemLpLoc P (DD a b c) UnforcedLeray.B0412.q0E)
    (hWU : ∀ a b, WeakDyS P a (U b) (D a b))
    (hWD : ∀ a b c, WeakDyS P b (D a c) (DD a b c))
    (Φ : ℝ × UnforcedLeray.Space → CVec3) (hΦ : IsPhaseTest P Φ) (j : Fin 3) :
    pairF P (advT (fun x => WithLp.toLp 2 (fun i => U i x)) (dy j Φ))
        (fun x => WithLp.toLp 2 (fun i => U i x)) =
      -pairF P Φ (fun x => WithLp.toLp 2 (fun i => -∑ k : Fin 3,
        (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x))) := by
  have hU2' : ∀ i, MemLpLoc P (U i) 2 := fun i => memLpLoc_mono (hU2 i) two_le_two_mul_q0E
  have hD2' : ∀ a b, MemLpLoc P (D a b) 2 := fun a b => memLpLoc_mono (hD2 a b) two_le_two_mul_q0E
  have hDD2' : ∀ a b c, MemLpLoc P (DD a b c) 2 := fun a b c => memLpLoc_mono (hDD2 a b c) q0E_two_le
  have hDq : ∀ a b, MemLpLoc P (D a b) UnforcedLeray.B0412.q0E :=
    fun a b => memLpLoc_mono (hD2 a b) q0E_le_two_mul_q0E
  -- component test and its derivative
  have hφ : ∀ i, IsPhaseTest P (fun y => Φ y i) := fun i => isPhaseTest_comp_coord hΦ i
  have hφd : ∀ i, IsPhaseTest P (dy j (fun y => Φ y i)) := fun i => (hφ i).dy j
  have hdyc : ∀ i, dy j (fun y => Φ y i) = fun y => dy j Φ y i := fun i =>
    funext fun y => dy_comp_coord hΦ.smooth j i y
  -- first integration by parts in `y_k` (WeakMulRule for `u_k u_i`)
  have hIBP1 : ∀ i k, phaseInt P (fun x => dy k (dy j (fun y => Φ y i)) x * (U k x * U i x)) =
      -phaseInt P (fun x => dy j (fun y => Φ y i) x *
        (D k k x * U i x + U k x * D k i x)) := by
    intro i k
    exact (weakMulRule : WeakMulRule) P k (fun x => U k x) (fun x => U i x) (D k k) (D k i)
      (hU2 k) (hU2 i) (hDq k k) (hDq k i) (hWU k k) (hWU k i) _ (hφd i)
  -- second integration by parts in `y_j` (test `Φ_i`)
  have hIBP2 : ∀ i k, phaseInt P (fun x => dy j (fun y => Φ y i) x *
      (D k k x * U i x + U k x * D k i x)) =
      -phaseInt P (fun x => Φ x i *
        (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x)) := by
    intro i k
    have hA : WeakDyS P j (fun x => D k k x * U i x)
        (fun x => DD k j k x * U i x + D k k x * D j i x) :=
      (weakMulRule : WeakMulRule) P j (D k k) (U i) (DD k j k) (D j i)
        (hD2 k k) (hU2 i) (hDD2 k j k) (hDq j i) (hWD k j k) (hWU j i)
    have hB : WeakDyS P j (fun x => U k x * D k i x)
        (fun x => D j k x * D k i x + U k x * DD k j i x) :=
      (weakMulRule : WeakMulRule) P j (U k) (D k i) (D j k) (DD k j i)
        (hU2 k) (hD2 k i) (hDq j k) (hDD2 k j i) (hWU j k) (hWD k j i)
    have hA' : phaseInt P (fun x => dy j (fun y => Φ y i) x * (D k k x * U i x)) =
        -phaseInt P (fun x => Φ x i * (DD k j k x * U i x + D k k x * D j i x)) :=
      hA _ (hφ i)
    have hB' : phaseInt P (fun x => dy j (fun y => Φ y i) x * (U k x * D k i x)) =
        -phaseInt P (fun x => Φ x i * (D j k x * D k i x + U k x * DD k j i x)) :=
      hB _ (hφ i)
    have int1 : Integrable (fun x => dy j (fun y => Φ y i) x * (D k k x * U i x))
        (volume.restrict (phaseCell P)) :=
      integrable_test_mul2 (hφd i) (hD2' k k) (hU2' i)
    have int2 : Integrable (fun x => dy j (fun y => Φ y i) x * (U k x * D k i x))
        (volume.restrict (phaseCell P)) :=
      integrable_test_mul2 (hφd i) (hU2' k) (hD2' k i)
    have intA : Integrable (fun x => Φ x i * (DD k j k x * U i x + D k k x * D j i x))
        (volume.restrict (phaseCell P)) :=
      integrable_test_mul_sum2 (hφ i) (hDD2' k j k) (hU2' i) (hD2' k k) (hD2' j i)
    have intB : Integrable (fun x => Φ x i * (D j k x * D k i x + U k x * DD k j i x))
        (volume.restrict (phaseCell P)) :=
      integrable_test_mul_sum2 (hφ i) (hD2' j k) (hD2' k i) (hU2' k) (hDD2' k j i)
    have hsplit : phaseInt P (fun x => dy j (fun y => Φ y i) x *
        (D k k x * U i x + U k x * D k i x)) =
        phaseInt P (fun x => dy j (fun y => Φ y i) x * (D k k x * U i x)) +
        phaseInt P (fun x => dy j (fun y => Φ y i) x * (U k x * D k i x)) := by
      rw [← phaseInt_add_cell int1 int2]
      congr 1
      funext x
      ring
    have hT : phaseInt P (fun x => Φ x i *
        (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x)) =
        phaseInt P (fun x => Φ x i * (DD k j k x * U i x + D k k x * D j i x)) +
        phaseInt P (fun x => Φ x i * (D j k x * D k i x + U k x * DD k j i x)) := by
      rw [← phaseInt_add_cell intA intB]
      congr 1
      funext x
      ring
    rw [hsplit, hA', hB', hT]
    ring
  -- expansion of the left side into the components
  have hpt : ∀ x, dotL (advT (fun x => WithLp.toLp 2 (fun i => U i x)) (dy j Φ) x)
      (WithLp.toLp 2 (fun i => U i x)) =
      ∑ i : Fin 3, ∑ k : Fin 3, dy k (dy j (fun y => Φ y i)) x * (U k x * U i x) := by
    intro x
    simp only [hdyc, advT, dotL_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, smul_eq_mul,
      Finset.sum_mul, PiLp.toLp_apply, Finset.sum_apply, Pi.smul_apply, PiLp.smul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [dy_comp_coord (hΦ.dy j).smooth k i x]
    ring
  have hL_expand : pairF P (advT (fun x => WithLp.toLp 2 (fun i => U i x)) (dy j Φ))
      (fun x => WithLp.toLp 2 (fun i => U i x)) =
      ∑ i : Fin 3, ∑ k : Fin 3, phaseInt P
        (fun x => dy k (dy j (fun y => Φ y i)) x * (U k x * U i x)) := by
    unfold pairF
    simp only [hpt]
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ k : Fin 3, dy k (dy j (fun y => Φ y i)) x * (U k x * U i x))
      (fun i _ => integrable_sum_cell Finset.univ (fun k _ =>
        integrable_test_mul2 (hφd i |>.dy k) (hU2' k) (hU2' i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun k x => dy k (dy j (fun y => Φ y i)) x * (U k x * U i x))
      (fun k _ => integrable_test_mul2 (hφd i |>.dy k) (hU2' k) (hU2' i))]
  -- the right side as a sum of phase integrals
  have hdotF : ∀ x, dotL (Φ x) (WithLp.toLp 2 (fun i => -∑ k : Fin 3,
      (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x))) =
      -∑ i : Fin 3, ∑ k : Fin 3, Φ x i *
        (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x) := by
    intro x
    simp only [dotL_apply, PiLp.toLp_apply, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  have hTint : ∀ i k, Integrable (fun x => Φ x i *
      (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x))
      (volume.restrict (phaseCell P)) := fun i k =>
    integrable_test_mul_sum4 (hφ i) (hDD2' k j k) (hU2' i) (hD2' k k) (hD2' j i)
      (hD2' j k) (hD2' k i) (hU2' k) (hDD2' k j i)
  have hGint : Integrable (fun x => ∑ i : Fin 3, ∑ k : Fin 3, Φ x i *
      (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x))
      (volume.restrict (phaseCell P)) :=
    integrable_sum_cell Finset.univ (fun i _ => integrable_sum_cell Finset.univ (fun k _ => hTint i k))
  have hRHS : -pairF P Φ (fun x => WithLp.toLp 2 (fun i => -∑ k : Fin 3,
      (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x))) =
      ∑ i : Fin 3, ∑ k : Fin 3, phaseInt P (fun x => Φ x i *
        (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x)) := by
    unfold pairF
    simp only [hdotF]
    rw [phaseInt_neg_cell hGint, neg_neg]
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ k : Fin 3, Φ x i *
        (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x))
      (fun i _ => integrable_sum_cell Finset.univ (fun k _ => hTint i k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun k x => Φ x i *
        (DD k j k x * U i x + D k k x * D j i x + D j k x * D k i x + U k x * DD k j i x))
      (fun k _ => hTint i k)]
  rw [hL_expand, hRHS]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hIBP1 i k, hIBP2 i k, neg_neg]

end UnforcedLeray.Short.PartIIIb.Concrete
