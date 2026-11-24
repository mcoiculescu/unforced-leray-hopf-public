import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part II-b, task `PartII-b:G4/3/6/2/2` (`RawPsiTailJets`): tail jets of the stream

Source of record: `the November 2 reference manuscript` (SP) 463-467
(`sct:transverse`, `ρ = 2`, `l = 0`, `S_* = Σ/ν`, `c = ν⁻²`), 255-258 (polynomial convention).
Proved here: `rawPsiTailJets_of`, from `PartI.TrainTransverseTails` applied three times
(`ℓ = 0, 1, 2`, `j = 0`), each time at `l = 0` where the exponential factor equals `2`, and the
polynomial `P_S = C((1+c+ν⁻¹)(1+S))^N` is bounded by a power of `ν⁻¹` at `c = ν⁻²`, `S = Σ/ν`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartI

/-- An auxiliary polynomial inequality in `t = ν⁻¹ ≥ 1`. -/
theorem tailAux_poly (t Sig : ℝ) (ht : 1 ≤ t) (hS : 0 ≤ Sig) :
    (1 + t ^ 2 + t) * (1 + Sig * t) ≤ 3 * (1 + Sig) * t ^ 3 := by
  have a1 : 1 + t ^ 2 + t ≤ 3 * t ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * t + 1) (sub_nonneg.2 ht)]
  have a2 : 1 + Sig * t ≤ (1 + Sig) * t := by nlinarith
  have a0 : 0 ≤ 1 + Sig * t := by nlinarith [mul_nonneg hS (by linarith : (0:ℝ) ≤ t)]
  calc (1 + t ^ 2 + t) * (1 + Sig * t) ≤ (3 * t ^ 2) * ((1 + Sig) * t) :=
        mul_le_mul a1 a2 a0 (by positivity)
    _ = 3 * (1 + Sig) * t ^ 3 := by ring

/-- `P_S = C((1+c+ν⁻¹)(1+S))^N` at `c = ν⁻²`, `S = Σ/ν`, `0 < ν ≤ 1`, multiplied by `2`, is at most
`2 C (3(1+Σ))^N ν^{-M}` for `M ≥ 3N`. -/
theorem polyPS_tail_le (C : ℝ) (N M : ℕ) (hC : 0 ≤ C) (hNM : 3 * N ≤ M) {ν Sig : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hSig : 0 ≤ Sig) :
    polyPS C N ν (ν ^ 2)⁻¹ (Sig / ν) * 2 ≤ 2 * (C * (3 * (1 + Sig)) ^ N) * (ν ^ M)⁻¹ := by
  have ht1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have ht0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hc : (ν ^ 2)⁻¹ = ν⁻¹ ^ 2 := (inv_pow ν 2).symm
  have hA : 0 ≤ C * (3 * (1 + Sig)) ^ N := mul_nonneg hC (pow_nonneg (by linarith) N)
  have hpoly : polyPS C N ν (ν ^ 2)⁻¹ (Sig / ν) ≤ C * (3 * (1 + Sig)) ^ N * ν⁻¹ ^ (3 * N) := by
    unfold polyPS
    rw [hc, div_eq_mul_inv]
    have hX := tailAux_poly ν⁻¹ Sig ht1 hSig
    have hnn : 0 ≤ (1 + ν⁻¹ ^ 2 + ν⁻¹) * (1 + Sig * ν⁻¹) :=
      mul_nonneg (by nlinarith) (by nlinarith [mul_nonneg hSig ht0])
    have hXN := pow_le_pow_left₀ hnn hX N
    calc C * ((1 + ν⁻¹ ^ 2 + ν⁻¹) * (1 + Sig * ν⁻¹)) ^ N
        ≤ C * (3 * (1 + Sig) * ν⁻¹ ^ 3) ^ N := mul_le_mul_of_nonneg_left hXN hC
      _ = C * (3 * (1 + Sig)) ^ N * ν⁻¹ ^ (3 * N) := by rw [mul_pow, ← pow_mul]; ring
  have hpow : ν⁻¹ ^ (3 * N) ≤ ν⁻¹ ^ M := pow_le_pow_right₀ ht1 hNM
  calc polyPS C N ν (ν ^ 2)⁻¹ (Sig / ν) * 2
      ≤ (C * (3 * (1 + Sig)) ^ N * ν⁻¹ ^ (3 * N)) * 2 :=
        mul_le_mul_of_nonneg_right hpoly (by norm_num)
    _ ≤ (C * (3 * (1 + Sig)) ^ N * ν⁻¹ ^ M) * 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA) (by norm_num)
    _ = 2 * (C * (3 * (1 + Sig)) ^ N) * (ν ^ M)⁻¹ := by rw [← inv_pow]; ring

/-- `trainPeriod 2 ν = (ν²)⁻¹` (`ν^(-2:ℝ)`). -/
theorem trainPeriod_two_eq_inv {ν : ℝ} (hν : 0 < ν) : trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- One tail jet `ℓ` of `ψ` (`j = 0`), from `PartI.TrainTransverseTails` at `ρ = 2`, `l = 0`:
the constants do not depend on the horizon `S_` nor on the train; the bound is
`polyPS C N ν c S_ · (e⁰ + e⁰) = 2 polyPS`. -/
theorem tailPsi_part (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) (ℓ : ℕ) :
    ∃ (C' C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C' ∧ 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
          ∀ S_ : ℝ, 0 ≤ S_ → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : UnforcedLeray.Cyl.Plane,
            C' / ν + 2 ≤ |z.2| →
              ‖ageJet ℓ 0 tr.ψ s z‖ ≤ polyPS C N ν c S_ * 2 := by
  obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, H⟩ := hT 2 (by norm_num) ℓ 0
  refine ⟨C', C, N, ν₀, hC', hC, hν₀, ?_⟩
  intro ν hν hνν₀ c hc tr htr S_ hS s hs hsS z hz
  have hc' : c = trainPeriod 2 ν := by rw [hc, trainPeriod_two_eq_inv hν]
  subst hc'
  have key := (H S_ hS ν hν hνν₀ tr htr 0 le_rfl s hs hsS z (by linarith)).1
  refine le_trans key (le_of_eq ?_)
  norm_num

end UnforcedLeray.Short.IIb

/-- **Tail jets of the stream** (SP 463-467 with `l = 0`, `S_* = Σ/ν`, `c = ν⁻²`): from
`PartI.TrainTransverseTails`, the jets `ψ, ∂_sψ, ∂_s²ψ` of `ψ` satisfy `RawPsiTailJets`. -/
theorem rawPsiTailJets_of (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) :
    UnforcedLeray.Short.IIb.RawPsiTailJets := by
  unfold UnforcedLeray.Short.IIb.RawPsiTailJets
  obtain ⟨C0, K0, N0, n0, hC0, hK0, hn0, H0⟩ :=
    UnforcedLeray.Short.IIb.tailPsi_part hT 0
  obtain ⟨C1, K1, N1, n1, hC1, hK1, hn1, H1⟩ :=
    UnforcedLeray.Short.IIb.tailPsi_part hT 1
  obtain ⟨C2, K2, N2, n2, hC2, hK2, hn2, H2⟩ :=
    UnforcedLeray.Short.IIb.tailPsi_part hT 2
  refine ⟨C0 + C1 + C2, by linarith, fun Sig hSig dm dp _ => ?_⟩
  have hM0 : 3 * N0 ≤ 3 * (N0 + N1 + N2) := by omega
  have hM1 : 3 * N1 ≤ 3 * (N0 + N1 + N2) := by omega
  have hM2 : 3 * N2 ≤ 3 * (N0 + N1 + N2) := by omega
  have h3 : (0:ℝ) < 3 * (1 + Sig) := by linarith
  refine ⟨2 * (K0 * (3 * (1 + Sig)) ^ N0) + 2 * (K1 * (3 * (1 + Sig)) ^ N1) +
      2 * (K2 * (3 * (1 + Sig)) ^ N2),
    3 * (N0 + N1 + N2), min (min n0 n1) (min n2 1),
    add_pos (add_pos (mul_pos two_pos (mul_pos hK0 (pow_pos h3 N0)))
      (mul_pos two_pos (mul_pos hK1 (pow_pos h3 N1))))
      (mul_pos two_pos (mul_pos hK2 (pow_pos h3 N2))),
    lt_min (lt_min hn0 hn1) (lt_min hn2 one_pos), ?_⟩
  intro p d hd hν hS' x hx0 hxH hη
  have hνp : 0 < p.ν := p.ν_pos
  have hn0' : p.ν ≤ n0 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hn1' : p.ν ≤ n1 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hn2' : p.ν ≤ n2 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hH : p.H = Sig / p.ν := by
    unfold UnforcedLeray.Cons.C03.Concrete.Params.H
    rw [hS']
  have hS0 : 0 ≤ Sig / p.ν := div_nonneg hSig.le hνp.le
  have hx : x.1 ≤ Sig / p.ν := by rw [← hH]; exact hxH
  have hη0 : C0 / p.ν + 2 ≤ |x.2.2| := by
    have : C0 / p.ν ≤ (C0 + C1 + C2) / p.ν :=
      div_le_div_of_nonneg_right (by linarith) hνp.le
    linarith
  have hη1 : C1 / p.ν + 2 ≤ |x.2.2| := by
    have : C1 / p.ν ≤ (C0 + C1 + C2) / p.ν :=
      div_le_div_of_nonneg_right (by linarith) hνp.le
    linarith
  have hη2 : C2 / p.ν + 2 ≤ |x.2.2| := by
    have : C2 / p.ν ≤ (C0 + C1 + C2) / p.ν :=
      div_le_div_of_nonneg_right (by linarith) hνp.le
    linarith
  have e0 := H0 p.ν hνp hn0' p.c hd.c_eq p.train hd.train_buc (Sig / p.ν) hS0 x.1 hx0 hx x.2 hη0
  have e1 := H1 p.ν hνp hn1' p.c hd.c_eq p.train hd.train_buc (Sig / p.ν) hS0 x.1 hx0 hx x.2 hη1
  have e2 := H2 p.ν hνp hn2' p.c hd.c_eq p.train hd.train_buc (Sig / p.ν) hS0 x.1 hx0 hx x.2 hη2
  have b0 := UnforcedLeray.Short.IIb.polyPS_tail_le K0 N0 (3 * (N0 + N1 + N2)) hK0.le hM0 hνp hν1 hSig.le
  have b1 := UnforcedLeray.Short.IIb.polyPS_tail_le K1 N1 (3 * (N0 + N1 + N2)) hK1.le hM1 hνp hν1 hSig.le
  have b2 := UnforcedLeray.Short.IIb.polyPS_tail_le K2 N2 (3 * (N0 + N1 + N2)) hK2.le hM2 hνp hν1 hSig.le
  rw [← hd.c_eq] at b0 b1 b2
  have A0 := le_trans e0 b0
  have A1 := le_trans e1 b1
  have A2 := le_trans e2 b2
  rw [add_mul, add_mul]
  exact add_le_add (add_le_add A0 A1) A2
