import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.L2Org

/-!
# `PartIII-b:C/rep/8/2/3/3`: the pointwise weighted train bound with every transverse weight

Source of record: `the November 2 reference manuscript` (73 pages), 5464-5465,
5477-5482 (the weighted train coefficient and its `L²` norm: "the remaining powers `s^{7/2}` ...
are integrable at zero ... Gaussian moments of fixed order"), 5484-5495 (young train), Part I
`sct:transverse` 460-467 and `sct:fixed-band` 468-478.

`L2Org.lean` reduces `TML2` to `TMPtW 5` (`tmL2_of_pt5`): the pointwise bound of
`𝔴_5 = (1+|η|)𝔴_4`, one transverse power more than `TMPt = TMPtW 4`.  The organization of `TMPt`
(`PtOrg.lean`, task `PartIII-b:C/rep/8/2/3/2`) fixes the transverse weight `(1+|η|)^4` in exactly
four places: the tails `TailW`, the weighted age jets `WJetV`, `WJetP`, `WJetPsi`, and the weighted
dilation jets `WDil`.  The weight is free in the source: the transverse tails of `sct:transverse`
are `P_S(e^{-bl/c} + e^{-bl²/(C₀+νS)})` beyond `|η| ≥ C'/ν + 2 + l` (`c = ν⁻²`, `S = 1/ν`), so
`(1+|η|)^w` costs `w!`-type constants and a polynomial in `1/ν` (`l^w e^{-x l} ≤ w! x^{-w}`), and in
the band `|η| < C_p/ν + 2` the weight is `≤ (C_p + 3)^w ν^{-w}`.  Here those four Props are stated
for every weight `w` (`TailWW`, `WJetVW`, `WJetPW`, `WJetPsiW`, `WDilW`); the unweighted leaves of
`PtOrg.lean` (`DilJetBound`, `JointAgeVec`, `SupV`, `BandP`, `StreamShift`, `EtaSegment`, ...) are
reused as they are.  The `w = 4` instances are the Props of `PtOrg.lean`.

**Proved here:** `tmPtW_of` (assembly along the sequence, the proof of `tmPt_of` with weight `w`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- **Weighted tails, every weight** (Part I `sct:transverse`, source 460-467, with `S_* = 1/ν`,
`c = ν⁻²`, `l = |η| - C_p/ν - 2`): for `|η| ≥ C_p/ν + 2`, `(1+|η|)^w` times the jets `∂_s^ℓ D^m` of
`v, p, ψ` is `≤ Cν^{-k}` on `0 < s ≤ 1/ν`.  `w = 4` is `TailW`. -/
def TailWW : Prop :=
  ∀ w ℓ m : ℕ, ∃ (Cp C : ℝ) (k : ℕ) (a : ℝ), 0 < Cp ∧ 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane, Cp / ν + 2 ≤ |z.2| →
        (1 + |z.2|) ^ w * (‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ +
          ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z‖ +
          ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z‖) ≤ C * ν⁻¹ ^ k

/-- **Weighted velocity jets, every weight** (source 5477-5482, 5484-5495, 460-478):
`(1+|η|)^w‖∂_s^ℓD^m v‖ ≤ Cν^{-k}` on `0 < s ≤ 1/ν`, every `z`.  `w = 4` is `WJetV`. -/
def WJetVW : Prop :=
  ∀ w ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        (1 + |z.2|) ^ w * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ ≤ C * ν⁻¹ ^ k

/-- **Weighted pressure jets, every weight** (as `WJetVW`, for the decaying pressure
`p_cyl = tr.p`).  `w = 4` is `WJetP`. -/
def WJetPW : Prop :=
  ∀ w ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        (1 + |z.2|) ^ w * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z‖ ≤ C * ν⁻¹ ^ k

/-- **Weighted stream jets, every weight** (as `WJetVW`, for the decaying stream `ψ = tr.ψ`).
`w = 4` is `WJetPsi`. -/
def WJetPsiW : Prop :=
  ∀ w ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        (1 + |z.2|) ^ w * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z‖ ≤ C * ν⁻¹ ^ k

/-- **Weighted dilation jets of one train field, every weight** (`F = trainFv, trainFp,
trainFpsi`; source 5464-5465, 5477-5482): `(1+|η|)^w‖D^j_{(σ,q,η)}F(log s, q, η)‖ ≤ Cν^{-k}` for
`j ≤ 4`, `0 < s ≤ 1/ν`, uniformly over the levels with a BUC train and `ν ≤ a`.  `w = 4` is
`WDil F`. -/
def WDilW {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ReturnLevel → ℝ × (ℝ × ℝ) → E) : Prop :=
  ∀ w : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ L : ReturnLevel,
    UnforcedLeray.Short.PartI.IsBUCTrain L.train → L.ν ≤ a → ∀ j : ℕ, j < 5 →
      ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
        (1 + |p.2.2|) ^ w * ‖iteratedFDeriv ℝ j (F L) (Real.log p.1, p.2)‖ ≤ C * L.ν⁻¹ ^ k

/-- **`TMPtW w` from the three weighted dilation bounds** (source 5464-5465, 5477-5482): the proof
of `tmPt_of` with the transverse weight `(1+|η|)^w`. -/
theorem tmPtW_of (D : SeqData) {dm dp : ℝ} (hv : WDilW trainFv) (hp : WDilW trainFp)
    (hψ : WDilW trainFpsi) (w : ℕ) : TMPtW w D dm dp := by
  intro hst
  obtain ⟨C1, k1, a1, ha1, H1⟩ := hv w
  obtain ⟨C2, k2, a2, ha2, H2⟩ := hp w
  obtain ⟨C3, k3, a3, ha3, H3⟩ := hψ w
  refine ⟨5 * (|C1| + |C2| + |C3|), k1 + k2 + k3, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < min a1 (min a2 a3) :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (lt_min ha1 (lt_min ha2 ha3)))
  filter_upwards [hst.actual, hsmall,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with n hact hsm hle
  intro p hp0 hp1
  have hbuc : UnforcedLeray.Short.PartI.IsBUCTrain (D.level n).train := hact.regime.train_buc
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1 : (D.level n).ν ≤ 1 := hle.1
  have hx : (1 : ℝ) ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hνa1 : (D.level n).ν ≤ a1 := (lt_of_lt_of_le hsm (min_le_left _ _)).le
  have hνa2 : (D.level n).ν ≤ a2 :=
    (lt_of_lt_of_le hsm ((min_le_right _ _).trans (min_le_left _ _))).le
  have hνa3 : (D.level n).ν ≤ a3 :=
    (lt_of_lt_of_le hsm ((min_le_right _ _).trans (min_le_right _ _))).le
  have mono : ∀ (C : ℝ) (k : ℕ), k ≤ k1 + k2 + k3 →
      C * (D.level n).ν⁻¹ ^ k ≤ |C| * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) := by
    intro C k hk
    calc C * (D.level n).ν⁻¹ ^ k ≤ |C| * (D.level n).ν⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hk) (abs_nonneg C)
  unfold trainWeight
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range 5, (1 + |p.2.2|) ^ w *
      (‖iteratedFDeriv ℝ j (trainFv (D.level n)) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFp (D.level n)) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFpsi (D.level n)) (Real.log p.1, p.2)‖) ≤
      (|C1| + |C2| + |C3|) * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) := by
    intro j hj
    have hj5 : j < 5 := Finset.mem_range.1 hj
    have e1 := (H1 (D.level n) hbuc hνa1 j hj5 p hp0 hp1).trans (mono C1 k1 (by omega))
    have e2 := (H2 (D.level n) hbuc hνa2 j hj5 p hp0 hp1).trans (mono C2 k2 (by omega))
    have e3 := (H3 (D.level n) hbuc hνa3 j hj5 p hp0 hp1).trans (mono C3 k3 (by omega))
    rw [mul_add, mul_add]
    have := add_le_add (add_le_add e1 e2) e3
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **`TML2` from the weight-general dilation bounds** (`tmL2_of_pt5` at `w = 5`). -/
theorem tmL2_of_wdil (D : SeqData) {dm dp : ℝ} (hv : WDilW trainFv) (hp : WDilW trainFp)
    (hψ : WDilW trainFpsi) : TML2 D dm dp :=
  tmL2_of_pt5 D (tmPtW_of D hv hp hψ 5)

end UnforcedLeray.Short.PartIIIb.Concrete
