import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# Decomposition of `velWeightedSup_of` (task `PartIII-b:C/rep/8/2/pres/4/2/1/1/1`)

Source `the November 2 reference manuscript`
2715-2725 (`sup √s W|v| ≤ P_ν`, `W ≥ 1`).

Young ages `0 < s ≤ 1/ν`: `SupV` (Part I `sct:fixed-band`, 468-478, task `PartIII-b:C/rep/8/2/3/2/8`),
with `√s ≤ ν⁻¹`.  Late ages `s > 1/ν`: `LateVelSup` below (Part I `sct:expansion` 447-459, `b = 1`,
`m = 0`, `p = ∞`: the mean velocity `-∂_η S` is `≤ P(1+s)^{-1}`; and `sct:fluctuation` 439-446:
the fluctuation is `≤ P e^{-κνs/c²}`, `c = ν⁻²`, so `√s·` it is `≤ P'`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace VelSupSub

/-- **Late-age velocity sup** (source 2715-2725; Part I `sct:expansion` 447-459 for the mean part
`v̄ = -∂_η S`, `(1+s)^{-1}` decay, and `sct:fluctuation` 439-446 for `ṽ`, `e^{-κνs/c²}` decay with
`c = ν⁻²`): `√s ‖v(s,z)‖ ≤ Cν^{-k}` for every `s > 1/ν`, every `z`, every BUC train at
`(ν, cOf ν)`, `ν ≤ a`. -/
def LateVelSup : Prop :=
  ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 1 / ν < s → ∀ z : UnforcedLeray.Cyl.Plane,
        Real.sqrt s * ‖tr.v s z‖ ≤ C * ν⁻¹ ^ k

end VelSupSub

open VelSupSub

theorem velWeightedSup_of_sub (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hE : SupV) (hL : LateVelSup) : RawSupOrg.VelWeightedSup D := by
  obtain ⟨C1, k1, a1, ha1, hA⟩ := hL
  obtain ⟨C2, k2, a2, ha2, hB⟩ := hE 0 0
  have hνt : Tendsto (fun n => retNu D.Pl D.σ₀ n) atTop (nhds 0) := retNu_tendsto D.σ₀ hst.omega_ne
  have hev : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ min (min a1 a2) 1 :=
    hνt.eventually (ge_mem_nhds (lt_min (lt_min ha1 ha2) one_pos))
  refine ⟨|C1| + |C2|, max k1 (k2 + 1), ?_⟩
  filter_upwards [hev] with n hn s hs z
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1 : (D.level n).ν ≤ 1 := hn.trans (min_le_right _ _)
  have hνa1 : (D.level n).ν ≤ a1 := hn.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνa2 : (D.level n).ν ≤ a2 := hn.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ha : (1 : ℝ) ≤ (D.level n).ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hν1⟩
  set a := (D.level n).ν⁻¹ with hadef
  have hapos : 0 < a := by linarith
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  by_cases hs1 : 1 / (D.level n).ν < s
  · have h := hA (D.level n).ν hνpos hνa1 (D.train n) (D.train_buc n) s hs1 z
    refine h.trans ?_
    calc C1 * a ^ k1 ≤ |C1| * a ^ k1 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ (|C1| + |C2|) * a ^ (max k1 (k2 + 1)) := by
          refine mul_le_mul ?_ (pow_le_pow_right₀ ha (le_max_left _ _)) (by positivity)
            (by positivity)
          linarith [abs_nonneg C2]
  · push_neg at hs1
    have h := hB (D.level n).ν hνpos hνa2 (D.train n) (D.train_buc n) s hs hs1 z
    have h0 : ‖UnforcedLeray.Short.PartI.ageJet 0 0 (D.train n).v s z‖ = ‖(D.train n).v s z‖ := by
      simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero,
        norm_iteratedFDeriv_zero]
    rw [h0] at h
    have hsa : Real.sqrt s ≤ a := by
      have : s ≤ a := by rw [hadef]; simpa [one_div] using hs1
      calc Real.sqrt s ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = a := Real.sqrt_sq hapos.le
    calc Real.sqrt s * ‖(D.train n).v s z‖ ≤ a * (C2 * a ^ k2) :=
          mul_le_mul hsa h (norm_nonneg _) hapos.le
      _ ≤ a * (|C2| * a ^ k2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
            hapos.le
      _ = |C2| * a ^ (k2 + 1) := by ring
      _ ≤ (|C1| + |C2|) * a ^ (max k1 (k2 + 1)) := by
          refine mul_le_mul ?_ (pow_le_pow_right₀ ha (le_max_right _ _)) (by positivity)
            (by positivity)
          linarith [abs_nonneg C1]

end UnforcedLeray.Short.PartIIIb.Concrete
