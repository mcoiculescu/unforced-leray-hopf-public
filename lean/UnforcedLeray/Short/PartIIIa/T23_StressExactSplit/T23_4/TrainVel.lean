import UnforcedLeray.Short.PartIIIa.Sub.T23_4_Leaves

/-!
# Part III-a, task `PartIII-a:T23/4/1`: transverse tail of the planar train velocity

Source of record: `the November 2 reference manuscript`, lines 2739-2756
(`stress-short:transverse`, the `|v_flat|` part, SP 2745-2753) and 463-467 (`sct:transverse`).

Proves `trainVelTransverseTail_of`: from the uniform Part I tails `TrainTransverseTailsUniform`
(velocity conjunct at `(ℓ,j) = (0,0)`) and the absorption `TailAbsorb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

theorem trainVelTransverseTail_of (hT : UnforcedLeray.Short.IIIa.TrainTransverseTailsUniform)
    (hK : UnforcedLeray.Short.IIIa.TailAbsorb) :
    UnforcedLeray.Short.IIIa.TrainVelTransverseTail := by
  intro dm dp hdm mZ hmZ bexp D hb hD
  obtain ⟨b, C₀, C', C, N, ν₁, hb', hC₀, hC', hC, hν₁, hT'⟩ := hT 2 (by norm_num) 0 0
  obtain ⟨Cp, ν₂, hCp, hν₂, hK'⟩ := hK b C₀ C' C (bexp * max dp 0) D N 1 ⌈mZ / 2⌉₊ hb' hC₀ hD
    (mul_nonneg hb.le (le_max_right _ _))
  refine ⟨Cp, min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hd hν pt hs hsS hη => ?_⟩
  obtain ⟨s, q, η⟩ := pt
  have hs' : 0 < s := hs
  have hsS' : s < p.ε ^ (-bexp) := hsS
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hmZ0 : 0 ≤ mZ := by linarith
  have hpc : p.c = UnforcedLeray.Short.PartI.trainPeriod 2 p.ν := by
    rw [hd.c_eq]
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg p.ν_pos.le, Real.rpow_two]
  have hdnn : 0 ≤ d := le_trans hd.dm_pos.le hd.dm_le
  set S := p.ε ^ (-bexp) with hSdef
  have hSeq : S = Real.exp (bexp * d / p.ν) := by
    rw [hSdef, Real.rpow_def_of_pos p.ε_pos, hd.eps_eq, Real.log_exp]
    congr 1
    ring
  have hS1 : 1 ≤ S := by
    rw [hSeq]
    exact Real.one_le_exp (div_nonneg (mul_nonneg hb.le hdnn) hνpos.le)
  have hSK : S ≤ Real.exp (bexp * max dp 0 / p.ν) := by
    rw [hSeq]
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hνpos.le
    exact mul_le_mul_of_nonneg_left (le_max_of_le_left hd.le_dp) hb.le
  rw [hd.c_eq] at hη
  have hthr : Cp * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) < |η| := hη
  obtain ⟨hl, hmain⟩ := hK' p.ν hνpos hν2 S hS1 hSK η hthr
  have hlpos : 0 ≤ |η| - C' / p.ν - 2 := by linarith
  have hT2 := hT' p.ν hνpos hν1 p.c hpc p.train hd.train_buc S (by linarith)
    (|η| - C' / p.ν - 2) hlpos s hs' hsS'.le (q, η)
    (by show C' / p.ν + 2 + (|η| - C' / p.ν - 2) ≤ |η|; linarith)
  dsimp only at hT2
  obtain ⟨_, hv, _, _⟩ := hT2
  have hKeq : UnforcedLeray.Short.PartI.polyPS C N p.ν p.c S *
      (Real.exp (-(b * (|η| - C' / p.ν - 2) / p.c)) +
        Real.exp (-(b * (|η| - C' / p.ν - 2) ^ 2 / (C₀ + p.ν * S)))) =
      UnforcedLeray.Short.PartI.polyPS C N p.ν (p.ν ^ 2)⁻¹ S *
      (Real.exp (-(b * (|η| - C' / p.ν - 2) / (p.ν ^ 2)⁻¹)) +
        Real.exp (-(b * (|η| - C' / p.ν - 2) ^ 2 / (C₀ + p.ν * S)))) := by
    rw [hd.c_eq]
  rw [hKeq] at hv
  have hvn := T23Tail.norm_ageJet_zero_zero p.train.v s (q, η)
  have hv2 := hv
  rw [hvn] at hv2
  have hsq : Real.sqrt s ≤ 1 + S := by
    calc Real.sqrt s ≤ Real.sqrt ((1 + S) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + S := Real.sqrt_sq (by linarith)
  have hW := T23Tail.transWeight_le_jap hmZ0 hs'.le q η
  have hWn := T23Tail.transWeight_nonneg mZ (s, (q, η))
  have hnv := norm_nonneg (p.train.v s (q, η))
  have ha : Real.sqrt s * transWeight mZ (s, (q, η)) ≤ (1 + S) * (1 + η ^ 2) ^ ⌈mZ / 2⌉₊ :=
    mul_le_mul hsq hW hWn (by linarith)
  have key := mul_le_mul ha hv2 hnv (mul_nonneg (by linarith) (by positivity))
  show Real.sqrt s * transWeight mZ (s, (q, η)) * ‖p.train.v s (q, η)‖ ≤ Real.exp (-D / p.ν) / 2
  refine key.trans ?_
  rw [pow_one] at hmain
  exact hmain

end UnforcedLeray.Short.IIIa
