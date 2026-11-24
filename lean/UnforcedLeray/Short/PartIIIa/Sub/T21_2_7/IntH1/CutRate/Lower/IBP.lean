import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutIBP
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutRateIntegrable

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutLowerIBPAux

lemma re_conj_comm (a b : ℂ) : ((starRingEnd ℂ) a * b).re = ((starRingEnd ℂ) b * a).re := by
  rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]

lemma re_conj_self (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

lemma re_conj_mul_ofReal_add (Φv z0 z1 : ℂ) (a0 a1 : ℝ) :
    ((starRingEnd ℂ) Φv * ((a0 : ℂ) * z0 + (a1 : ℂ) * z1)).re =
      a0 * ((starRingEnd ℂ) z0 * Φv).re + a1 * ((starRingEnd ℂ) z1 * Φv).re := by
  rw [mul_add, Complex.add_re]
  have e : ∀ (a : ℝ) (z : ℂ), ((starRingEnd ℂ) Φv * ((a : ℂ) * z)).re =
      a * ((starRingEnd ℂ) Φv * z).re := by
    intro a z
    rw [show (starRingEnd ℂ) Φv * ((a : ℂ) * z) = (a : ℂ) * ((starRingEnd ℂ) Φv * z) by ring,
      Complex.re_ofReal_mul]
  rw [e, e, re_conj_comm Φv z0, re_conj_comm Φv z1]

end CutLowerIBPAux

open CutLowerIBPAux in
/-- **(iii) One integration by parts in `x`** (SP 3060-3067): the Tasks-proved identity `cutIBP`
with `F = Φ` gives `2∑_k G_k + 2 ∫ χ_R² jb^{-m} Re(Φ̄ΔΦ) + 2∑_k P_k = 0`, where
`P_k = ∫ ∂_k w Re(Φ̄ ∂_kΦ)`; the weight-gradient term is `J = ∑_k P_k`. -/
theorem cutLowerIBP (m : ℝ) : CutLowerIBP m := by
  intro ν tr t s G φ M hL R hR ρ hρ
  obtain ⟨hctx, _, _⟩ := hL
  obtain ⟨hν, hν1, hb, ht, hts, hG, hφ, hj⟩ := id hctx
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hΦs : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hΦc : Continuous (φ ρ) := hΦs.continuous
  have hper : ∀ x : ℝ × ℝ, φ ρ (x.1 + ν ^ (-2 : ℝ), x.2) = φ ρ x :=
    hφ.periodic ρ (Ioo_subset_Ico_self hρ)
  have hfM : MemLp (φ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    hφ.memX ρ (Ioo_subset_Icc_self hρ)
  have hIBP := cutIBP (ν ^ (-2 : ℝ)) m R (φ ρ) (φ ρ) hc hR hΦs hΦs hper hper
  have hI := (cutRateIntegrable m (ν ^ (-2 : ℝ)) R (φ ρ) (φ ρ) (φ ρ) hc hR hΦs hΦc hΦc
    hfM).2.1
  have eG : ∀ k : Fin 2, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * (2 * ((starRingEnd ℂ) (pdCx k (φ ρ) x) *
        pdCx k (φ ρ) x).re)) = 2 * cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ := by
    intro k
    unfold cutGReal
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [re_conj_self]
    ring
  simp only [Fin.sum_univ_two] at hIBP
  unfold cutRate at hIBP
  simp only [Fin.sum_univ_two] at hIBP
  rw [eG 0, eG 1] at hIBP
  have hL2 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF2 m R φ ρ x =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        ((starRingEnd ℂ) (ladLapCx (φ ρ) x) * φ ρ x).re) := by
    congr 1
    funext x
    unfold lowF2
    rw [re_conj_comm]
  have hJ : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R φ ρ x =
      (∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.pd 0 (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx 0 (φ ρ) x) * φ ρ x).re) +
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), B0579.pd 1 (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx 1 (φ ρ) x) * φ ρ x).re := by
    rw [← integral_add (hI 0) (hI 1)]
    congr 1
    funext x
    exact re_conj_mul_ofReal_add (φ ρ x) (pdCx 0 (φ ρ) x) (pdCx 1 (φ ρ) x) _ _
  rw [Fin.sum_univ_two, hL2, hJ]
  linarith [hIBP]

end UnforcedLeray.Short.IIIa
