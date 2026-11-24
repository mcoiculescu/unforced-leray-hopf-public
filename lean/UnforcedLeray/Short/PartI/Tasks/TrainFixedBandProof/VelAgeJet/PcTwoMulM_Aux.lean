import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.T25_3_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.TtComp_Aux

/-!
# `PartI:T25/3/1`: Weight-`2m` polynomial bound for `ageJet ℓ k (pc ν c) s` (`TrainFixedBandPcAgeJetTwoMulM`)

Source of record: `the November 2 reference manuscript`, lines 468–478, 543–551,
4963–4968.

Proves `TrainFixedBandPcAgeJetTwoMulM`: for every `Sg > 0` and `m, ℓ, k : ℕ`, there exist `C > 0`
and `N : ℕ` such that for `0 < ν ≤ 1`, `0 < c`, `1 + Sg ≤ c ^ 2`, and `0 < s ≤ Sg / ν`,
`wCellL2 c (2 * m) (ageJet ℓ k (pc ν c) s) ≤ ENNReal.ofReal (polyP C N ν c)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI.VelAgeJetAux
open UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (pc jap wCellL2)

namespace PcTwoMulMAux

/-- Joint spacetime derivative bound for `pc ν c` on `0 < s ≤ Sg / ν` with transverse polynomial
weight `(1 + η ^ 2) ^ w`. -/
theorem pcJointJetSg (Sg : ℝ) (hSg : 0 < Sg) (w n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ν c : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 1 + Sg ≤ c ^ 2 →
        ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ Sg / ν →
          (1 + y.2.2 ^ 2) ^ w *
            ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => pc ν c x.1 x.2) y‖ ≤ K := by
  choose KE hKE0 hKE using pcEnvJetSg Sg hSg w
  choose KT hKT0 hKT using ttCompJetSg Sg hSg
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * KE i * KT (n - i),
    Finset.sum_nonneg fun i _ => by
      have := hKE0 i
      have := hKT0 (n - i)
      positivity, ?_⟩
  intro ν c hν0 hν1 hc hac y hy0 hy1
  set U : Set (ℝ × Plane) := Ioi (0 : ℝ) ×ˢ (univ : Set Plane)
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hU : UniqueDiffOn ℝ U := hUo.uniqueDiffOn
  have hy : y ∈ U := ⟨hy0, mem_univ _⟩
  have hpos : ∀ x : ℝ × Plane, x ∈ U → 0 < 1 + ν * x.1 := by
    intro x hx
    have := mul_pos hν0 hx.1
    linarith
  have hc1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => 1 + ν * x.1) U := by
    fun_prop
  have hc3 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ((1 + ν * x.1) ^ 3)⁻¹) U :=
    (hc1.pow 3).inv fun x hx => pow_ne_zero _ (hpos x hx).ne'
  have hexp : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U := by
    refine ContDiffOn.exp ?_
    refine ContDiffOn.div ?_ ?_ fun x hx => ?_
    · fun_prop
    · exact contDiffOn_const.mul hc1
    · exact (mul_pos two_pos (hpos x hx)).ne'
  have hE : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1))))
      U :=
    hc3.neg.mul hexp
  have hm : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U := by
    refine ContDiffOn.prodMk ?_ (by fun_prop)
    exact (contDiffOn_const.mul hc1).inv fun x hx => (mul_pos two_pos (hpos x hx)).ne'
  have hmaps : MapsTo (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      U {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx
    show 0 < (2 * (1 + ν * x.1))⁻¹
    exact inv_pos.2 (mul_pos two_pos (hpos x hx))
  have hT : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U :=
    (UnforcedLeray.Short.IIb.contDiffOn_tt_infty hc.ne' 0).comp hm hmaps
  have hEq : EqOn (fun x : ℝ × Plane => pc ν c x.1 x.2)
      (fun x : ℝ × Plane =>
        (-((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) *
          UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U :=
    fun x hx => PartI_T25_3.pc_theta_eq hν0 hc hx.1.le x.2
  have hconv : ∀ (i : ℕ) (F : ℝ × Plane → ℝ),
      iteratedFDerivWithin ℝ i F U y = iteratedFDeriv ℝ i F y :=
    fun i F => iteratedFDerivWithin_of_isOpen i hUo hy
  have hcongr : iteratedFDerivWithin ℝ n (fun x : ℝ × Plane => pc ν c x.1 x.2) U y
      = iteratedFDerivWithin ℝ n (fun x : ℝ × Plane =>
            (-((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) *
              UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U y :=
    iteratedFDerivWithin_congr hEq hy n
  have hL := norm_iteratedFDerivWithin_mul_le hE hT hU hy
    (n := n) (by exact_mod_cast le_top)
  have hLw := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (1 + y.2.2 ^ 2) ^ w)
  rw [Finset.mul_sum] at hLw
  have key : ∀ i ∈ Finset.range (n + 1),
      (1 + y.2.2 ^ 2) ^ w *
        ((n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i
            (fun x : ℝ × Plane =>
              -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U y‖ *
          ‖iteratedFDerivWithin ℝ (n - i)
            (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
            U y‖)
      ≤ (n.choose i : ℝ) * KE i * KT (n - i) := by
    intro i _hi
    have ha : (1 + y.2.2 ^ 2) ^ w *
        ‖iteratedFDerivWithin ℝ i
          (fun x : ℝ × Plane =>
            -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U y‖
        ≤ KE i := by
      rw [hconv]
      exact hKE i ν hν0 hν1 y hy0 hy1
    have hb : ‖iteratedFDerivWithin ℝ (n - i)
        (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
        U y‖ ≤ KT (n - i) := by
      rw [hconv]
      exact hKT (n - i) ν c hν0 hν1 hc hac y hy0 hy1
    have hc0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    have hKEi := hKE0 i
    calc (1 + y.2.2 ^ 2) ^ w *
          ((n.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i
              (fun x : ℝ × Plane =>
                -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U y‖ *
            ‖iteratedFDerivWithin ℝ (n - i)
              (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
              U y‖)
        = (n.choose i : ℝ) *
            ((1 + y.2.2 ^ 2) ^ w *
              ‖iteratedFDerivWithin ℝ i
                (fun x : ℝ × Plane =>
                  -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) U y‖) *
            ‖iteratedFDerivWithin ℝ (n - i)
              (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
              U y‖ := by ring
      _ ≤ (n.choose i : ℝ) * KE i * KT (n - i) :=
          mul_le_mul (mul_le_mul_of_nonneg_left ha hc0) hb (norm_nonneg _)
            (mul_nonneg hc0 hKEi)
  calc (1 + y.2.2 ^ 2) ^ w * ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => pc ν c x.1 x.2) y‖
      = (1 + y.2.2 ^ 2) ^ w *
          ‖iteratedFDerivWithin ℝ n (fun x : ℝ × Plane => pc ν c x.1 x.2) U y‖ := by
        rw [hconv]
    _ = (1 + y.2.2 ^ 2) ^ w *
          ‖iteratedFDerivWithin ℝ n
            (fun x : ℝ × Plane =>
              (-((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) *
                UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) U y‖ := by
        rw [hcongr]
    _ ≤ _ := hLw
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * KE i * KT (n - i) :=
        Finset.sum_le_sum key

end PcTwoMulMAux

/-- **Proof of `TrainFixedBandPcAgeJetTwoMulM` (`PartI:T25/3/1`)**:
for every `Sg > 0` and `m, ℓ, k : ℕ`, there exist `C > 0` and `N : ℕ` such that for `0 < ν ≤ 1`,
`0 < c`, `1 + Sg ≤ c ^ 2`, and `0 < s ≤ Sg / ν`,
`wCellL2 c (2 * m) (ageJet ℓ k (pc ν c) s) ≤ ENNReal.ofReal (polyP C N ν c)`. -/
theorem trainFixedBandPcAgeJetTwoMulM_proof : TrainFixedBandPcAgeJetTwoMulM := by
  intro Sg hSg m ℓ k
  obtain ⟨K, hK0, hK⟩ := PcTwoMulMAux.pcJointJetSg Sg hSg (m + 1) (ℓ + k)
  set M : ℝ := K + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  refine ⟨M * (Real.pi + 1), 1, by positivity, ?_⟩
  intro ν c s hν hν1 hc hSg_c2 hs hs_le
  have hpt : ∀ z : Plane,
      Real.sqrt (jap (2 * m) z) * ‖ageJet ℓ k (pc ν c) s z‖ ≤ M * (1 + z.2 ^ 2)⁻¹ := by
    intro z
    have hjap_eq : Real.sqrt (jap (2 * m) z) = (1 + z.2 ^ 2) ^ m := by
      have hsq : jap (2 * m) z = ((1 + z.2 ^ 2) ^ m) ^ 2 := by
        unfold jap
        rw [mul_comm 2 m, pow_mul]
      rw [hsq, Real.sqrt_sq (by positivity)]
    have hA : ‖ageJet ℓ k (pc ν c) s z‖ ≤
        ‖iteratedFDeriv ℝ (ℓ + k) (fun x : ℝ × Plane => pc ν c x.1 x.2) (s, z)‖ :=
      PcTwoMulMAux.alj_main ℓ (pc ν c) (PartI_T25_3.smS_pc hν hc) k hs z
    have hJ : (1 + z.2 ^ 2) ^ (m + 1) *
        ‖iteratedFDeriv ℝ (ℓ + k) (fun x : ℝ × Plane => pc ν c x.1 x.2) (s, z)‖ ≤ K :=
      hK ν c hν hν1 hc hSg_c2 (s, z) hs hs_le
    have hprod : (1 + z.2 ^ 2) ^ (m + 1) * ‖ageJet ℓ k (pc ν c) s z‖ ≤ M := by
      calc (1 + z.2 ^ 2) ^ (m + 1) * ‖ageJet ℓ k (pc ν c) s z‖
          ≤ (1 + z.2 ^ 2) ^ (m + 1) *
              ‖iteratedFDeriv ℝ (ℓ + k) (fun x : ℝ × Plane => pc ν c x.1 x.2) (s, z)‖ :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ ≤ K := hJ
        _ ≤ M := by dsimp [M]; linarith
    rw [hjap_eq]
    have h1z_ne : 1 + z.2 ^ 2 ≠ 0 := by positivity
    calc (1 + z.2 ^ 2) ^ m * ‖ageJet ℓ k (pc ν c) s z‖
        = ((1 + z.2 ^ 2) ^ (m + 1) * ‖ageJet ℓ k (pc ν c) s z‖) * (1 + z.2 ^ 2)⁻¹ := by
          rw [pow_succ']
          field_simp
          ring
      _ ≤ M * (1 + z.2 ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hprod (by positivity)
  have hL2 := wCellL2_le_of_inv_one_add_sq hc.le hM_pos.le (2 * m) (ageJet ℓ k (pc ν c) s) hpt
  refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold polyP
  rw [pow_one]
  have hsq : c * (M ^ 2 * Real.pi) ≤ (M * (Real.pi + 1) * (1 + c + ν⁻¹)) ^ 2 := by
    have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : c ≤ 1 + c + ν⁻¹ := by linarith
    have h2 : 1 ≤ 1 + c + ν⁻¹ := by linarith
    have h3 : c ≤ (1 + c + ν⁻¹) ^ 2 := by nlinarith
    have h4 : Real.pi ≤ (Real.pi + 1) ^ 2 := by nlinarith
    calc c * (M ^ 2 * Real.pi)
        = M ^ 2 * Real.pi * c := by ring
      _ ≤ M ^ 2 * (Real.pi + 1) ^ 2 * (1 + c + ν⁻¹) ^ 2 := by
          apply mul_le_mul _ h3 hc.le (by positivity)
          exact mul_le_mul_of_nonneg_left h4 (sq_nonneg M)
      _ = (M * (Real.pi + 1) * (1 + c + ν⁻¹)) ^ 2 := by ring
  exact (Real.sqrt_le_iff).2 ⟨by positivity, hsq⟩

end UnforcedLeray.Short.PartI.VelAgeJetAux

end
