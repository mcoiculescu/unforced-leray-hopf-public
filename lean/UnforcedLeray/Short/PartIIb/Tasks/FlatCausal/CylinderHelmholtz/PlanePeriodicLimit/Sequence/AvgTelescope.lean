import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_1

/-!

Source: `the November 2 reference manuscript` lines 1933-1935.
Telescoping: `H(z + c e_q) - H(z) = N⁻¹ (G(z + (N+1) c e_q) - G(z - N c e_q))`, so the `L²` norm on
any window is at most `2 N⁻¹ ‖G‖₂` (translation invariance of Lebesgue measure).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Function
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Translation `z ↦ (z.1 + a, z.2)` preserves Lebesgue measure on the plane. -/
theorem ppl_mp_shift (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + a, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right (volume : Measure ℝ) a).prod (MeasurePreserving.id volume)

/-- Telescoping sum over `Icc (-N) N` in `ℤ`. -/
theorem ppl_tel_sum {E : Type*} [AddCommGroup E] (A : ℤ → E) (N : ℕ) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), A (j + 1) - ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), A j =
      A ((N : ℤ) + 1) - A (-(N : ℤ)) := by
  have himg : Finset.Icc (-(N : ℤ)) (N : ℤ) =
      (Finset.range (2 * N + 1)).image (fun k : ℕ => (k : ℤ) - N) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨(j + N).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  have hinj : Set.InjOn (fun k : ℕ => (k : ℤ) - N) (Finset.range (2 * N + 1) : Set ℕ) := by
    intro x _ y _ h
    have h' : (x : ℤ) = (y : ℤ) := sub_left_inj.mp h
    exact_mod_cast h'
  rw [himg, Finset.sum_image hinj, Finset.sum_image hinj]
  have hB : ∀ k : ℕ, A ((k : ℤ) - N + 1) = (fun k : ℕ => A ((k : ℤ) - N)) (k + 1) := by
    intro k
    simp only
    congr 1
    push_cast
    ring
  simp only [hB]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k : ℕ => A ((k : ℤ) - N)) (2 * N + 1)]
  have e1 : ((2 * N + 1 : ℕ) : ℤ) - N = (N : ℤ) + 1 := by push_cast; ring
  have e0 : ((0 : ℕ) : ℤ) - N = -(N : ℤ) := by simp
  simp only [e1, e0]

/-- The translate average difference, pointwise: a telescoped multiple of two translates. -/
theorem ppl_avg_diff (c : ℝ) (N : ℕ) (G : ℝ × ℝ → CMerid) (z : ℝ × ℝ) :
    ppAvg c N G (z.1 + c, z.2) - ppAvg c N G z =
      (N : ℂ)⁻¹ • (G (z.1 + ((N : ℝ) + 1) * c, z.2) - G (z.1 + (-(N : ℝ)) * c, z.2)) := by
  have h1 : ppAvg c N G (z.1 + c, z.2) =
      (N : ℂ)⁻¹ • ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (z.1 + ((j + 1 : ℤ) : ℝ) * c, z.2) := by
    unfold ppAvg
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    exact Prod.ext (by push_cast; ring) rfl
  have h2 : ppAvg c N G z =
      (N : ℂ)⁻¹ • ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (z.1 + ((j : ℤ) : ℝ) * c, z.2) := rfl
  have tel := ppl_tel_sum (fun j : ℤ => G (z.1 + ((j : ℤ) : ℝ) * c, z.2)) N
  have e1 : G (z.1 + (((N : ℤ) + 1 : ℤ) : ℝ) * c, z.2) = G (z.1 + ((N : ℝ) + 1) * c, z.2) := by
    congr 1
    exact Prod.ext (by push_cast; ring) rfl
  have e2 : G (z.1 + (((-(N : ℤ)) : ℤ) : ℝ) * c, z.2) = G (z.1 + (-(N : ℝ)) * c, z.2) := by
    congr 1
    exact Prod.ext (by push_cast; ring) rfl
  rw [h1, h2, ← smul_sub, tel, e1, e2]


set_option maxHeartbeats 1000000 in
/-- Task `PartII-b:T12/1/4/1/4` (`PPLAvgTelescope`). -/
theorem ppl_avg_telescope : UnforcedLeray.Short.IIb.PPLAvgTelescope := by
  intro c hc G hG N M hN
  have hGm : AEStronglyMeasurable G volume := hG.aestronglyMeasurable
  have hfunD : (fun z : ℝ × ℝ => ppAvg c N G (z.1 + c, z.2) - ppAvg c N G z) =
      fun z => (N : ℂ)⁻¹ • (G (z.1 + ((N : ℝ) + 1) * c, z.2) - G (z.1 + (-(N : ℝ)) * c, z.2)) :=
    funext (ppl_avg_diff c N G)
  rw [hfunD]
  have hG1 : AEStronglyMeasurable (fun z : ℝ × ℝ => G (z.1 + ((N : ℝ) + 1) * c, z.2)) volume :=
    hGm.comp_measurePreserving (ppl_mp_shift (((N : ℝ) + 1) * c))
  have hG2 : AEStronglyMeasurable (fun z : ℝ × ℝ => G (z.1 + (-(N : ℝ)) * c, z.2)) volume :=
    hGm.comp_measurePreserving (ppl_mp_shift ((-(N : ℝ)) * c))
  have hT1 : eLpNorm (fun z : ℝ × ℝ => G (z.1 + ((N : ℝ) + 1) * c, z.2)) 2 volume =
      eLpNorm G 2 volume :=
    eLpNorm_comp_measurePreserving hGm (ppl_mp_shift (((N : ℝ) + 1) * c))
  have hT2 : eLpNorm (fun z : ℝ × ℝ => G (z.1 + (-(N : ℝ)) * c, z.2)) 2 volume =
      eLpNorm G 2 volume :=
    eLpNorm_comp_measurePreserving hGm (ppl_mp_shift ((-(N : ℝ)) * c))
  have hK : ‖((N : ℂ))⁻¹‖ₑ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
    rw [← ofReal_norm_eq_enorm]
    congr 1
    simp
  have hs1 : eLpNorm (fun z : ℝ × ℝ => G (z.1 + ((N : ℝ) + 1) * c, z.2) -
        G (z.1 + (-(N : ℝ)) * c, z.2)) 2 (volume.restrict (ppWindow c M)) ≤
      eLpNorm (fun z : ℝ × ℝ => G (z.1 + ((N : ℝ) + 1) * c, z.2) -
        G (z.1 + (-(N : ℝ)) * c, z.2)) 2 volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hs2 : eLpNorm (fun z : ℝ × ℝ => G (z.1 + ((N : ℝ) + 1) * c, z.2) -
        G (z.1 + (-(N : ℝ)) * c, z.2)) 2 volume ≤
      eLpNorm (fun z : ℝ × ℝ => G (z.1 + ((N : ℝ) + 1) * c, z.2)) 2 volume +
        eLpNorm (fun z : ℝ × ℝ => G (z.1 + (-(N : ℝ)) * c, z.2)) 2 volume :=
    eLpNorm_sub_le hG1 hG2 one_le_two
  have hc1 : eLpNorm (fun z : ℝ × ℝ => (N : ℂ)⁻¹ •
        (G (z.1 + ((N : ℝ) + 1) * c, z.2) - G (z.1 + (-(N : ℝ)) * c, z.2))) 2
        (volume.restrict (ppWindow c M)) ≤
      ‖((N : ℂ))⁻¹‖ₑ * eLpNorm (fun z : ℝ × ℝ =>
        G (z.1 + ((N : ℝ) + 1) * c, z.2) - G (z.1 + (-(N : ℝ)) * c, z.2)) 2
        (volume.restrict (ppWindow c M)) :=
    eLpNorm_const_smul_le (c := (N : ℂ)⁻¹) (f := fun z : ℝ × ℝ =>
      G (z.1 + ((N : ℝ) + 1) * c, z.2) - G (z.1 + (-(N : ℝ)) * c, z.2))
  have hX : eLpNorm (fun z : ℝ × ℝ =>
        G (z.1 + ((N : ℝ) + 1) * c, z.2) - G (z.1 + (-(N : ℝ)) * c, z.2)) 2
        (volume.restrict (ppWindow c M)) ≤ eLpNorm G 2 volume + eLpNorm G 2 volume := by
    refine hs1.trans (hs2.trans (le_of_eq ?_))
    rw [hT1, hT2]
  have hsum := hc1.trans (mul_le_mul' le_rfl hX)
  rw [hK] at hsum
  have hfin : ENNReal.ofReal ((N : ℝ)⁻¹) * (eLpNorm G 2 volume + eLpNorm G 2 volume) =
      2 * ENNReal.ofReal ((N : ℝ)⁻¹) * eLpNorm G 2 volume := by
    ring
  rw [hfin] at hsum
  exact hsum

#print axioms UnforcedLeray.Short.IIb.ppl_avg_telescope
