import UnforcedLeray.Short.PartIIIa.Sub.T23_4_Leaves

/-!
# Part III-a, task `PartIII-a:T23/4/3`: transverse tail of the stream completion

Source of record: `the November 2 reference manuscript`, lines 2739-2756
(`stress-short:transverse`, SP 2754 "increasing `C_⊥` absorbs the fixed weights, derivative
budgets") and 463-467 (`sct:transverse`); the stream completion `H = (1-η∂_η-2s∂_s)ψ`.

Proves `raisedStreamTransverseTail_of`: three instances of the uniform Part I tails for
`ψ`, `∂_ηψ`, `∂_sψ` (jets `(0,0)`, `(0,1)`, `(1,0)`), absorbed by `TailAbsorb` at `D + 2`,
and `|H| ≤ |ψ| + |η||∂_ηψ| + 2s|∂_sψ|` (`abs_raisedStream_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

namespace T23RS

/-- Replacing the period `c` by `(ν²)⁻¹` inside the Part I tail bracket. -/
theorem K_eq (C : ℝ) (N : ℕ) (ν c S b l C₀ : ℝ) (h : c = (ν ^ 2)⁻¹) :
    UnforcedLeray.Short.PartI.polyPS C N ν c S *
        (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S)))) =
      UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
        (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S)))) := by
  subst h
  rfl

/-- `2 · (polyPS C · E) = polyPS (2C) · E`. -/
theorem polyPS_two (C : ℝ) (N : ℕ) (ν c S E : ℝ) :
    2 * (UnforcedLeray.Short.PartI.polyPS C N ν c S * E) =
      UnforcedLeray.Short.PartI.polyPS (2 * C) N ν c S * E := by
  unfold UnforcedLeray.Short.PartI.polyPS
  ring

/-- The numeric absorption `(3/2) e^{-(D+2)/ν} ≤ e^{-D/ν}/2` for `0 < ν ≤ 1`. -/
theorem three_half_le {D ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    3 / 2 * Real.exp (-(D + 2) / ν) ≤ Real.exp (-D / ν) / 2 := by
  have e1 : Real.exp (-(D + 2) / ν) = Real.exp (-D / ν) * Real.exp (-2 / ν) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-2 / ν) * Real.exp (2 / ν) = 1 := by
    rw [← Real.exp_add, show -2 / ν + 2 / ν = 0 by ring, Real.exp_zero]
  have e3 : 2 ≤ 2 / ν := by
    rw [le_div_iff₀ hν]
    linarith
  have e4 : 3 ≤ Real.exp (2 / ν) := by
    linarith [Real.add_one_le_exp (2 / ν)]
  have e5 : Real.exp (-2 / ν) ≤ 1 / 3 := by
    nlinarith [Real.exp_pos (-2 / ν), Real.exp_pos (2 / ν)]
  have hE := Real.exp_pos (-D / ν)
  rw [e1]
  nlinarith

/-- `|η| ≤ 1 + η²`. -/
theorem abs_le_one_add_sq (η : ℝ) : |η| ≤ 1 + η ^ 2 := by
  nlinarith [sq_nonneg (|η| - 1 / 2), sq_abs η]

/-- `√s ≤ 1 + S` for `s ≤ S`, `0 ≤ S`. -/
theorem sqrt_le_one_add {s S : ℝ} (hs : s ≤ S) (hS : 0 ≤ S) : Real.sqrt s ≤ 1 + S := by
  have hsq : s ≤ (1 + S) ^ 2 := by
    have e : (1 + S) ^ 2 = 1 + 2 * S + S * S := by ring
    have := mul_self_nonneg S
    linarith
  calc Real.sqrt s ≤ Real.sqrt ((1 + S) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 1 + S := Real.sqrt_sq (by linarith)

end T23RS

set_option maxHeartbeats 1000000 in
theorem raisedStreamTransverseTail_of (hT : UnforcedLeray.Short.IIIa.TrainTransverseTailsUniform)
    (hK : UnforcedLeray.Short.IIIa.TailAbsorb) :
    UnforcedLeray.Short.IIIa.RaisedStreamTransverseTail := by
  intro dm dp hdm mZ hmZ bexp D hb hD
  obtain ⟨b0, C₀0, C'0, C0, N0, nu0, hb0, hC₀0, hC'0, hC0, hnu0, hT0⟩ :=
    hT 2 (by norm_num) 0 0
  obtain ⟨b1, C₀1, C'1, C1, N1, nu1, hb1, hC₀1, hC'1, hC1, hnu1, hT1⟩ :=
    hT 2 (by norm_num) 0 1
  obtain ⟨b2, C₀2, C'2, C2, N2, nu2, hb2, hC₀2, hC'2, hC2, hnu2, hT2⟩ :=
    hT 2 (by norm_num) 1 0
  have hKn : 0 ≤ bexp * max dp 0 := mul_nonneg hb.le (le_max_right _ _)
  have hD2 : 0 < D + 2 := by linarith
  obtain ⟨Cq0, mu0, hCq0, hmu0, hK0⟩ :=
    hK b0 C₀0 C'0 C0 (bexp * max dp 0) (D + 2) N0 1 ⌈mZ / 2⌉₊ hb0 hC₀0 hD2 hKn
  obtain ⟨Cq1, mu1, hCq1, hmu1, hK1⟩ :=
    hK b1 C₀1 C'1 C1 (bexp * max dp 0) (D + 2) N1 1 (⌈mZ / 2⌉₊ + 1) hb1 hC₀1 hD2 hKn
  obtain ⟨Cq2, mu2, hCq2, hmu2, hK2⟩ :=
    hK b2 C₀2 C'2 (2 * C2) (bexp * max dp 0) (D + 2) N2 2 ⌈mZ / 2⌉₊ hb2 hC₀2 hD2 hKn
  have hVpos : 0 < min (min (min nu0 nu1) nu2) (min (min mu0 mu1) mu2) :=
    lt_min (lt_min (lt_min hnu0 hnu1) hnu2) (lt_min (lt_min hmu0 hmu1) hmu2)
  refine ⟨max (max Cq0 Cq1) Cq2,
    min (min (min (min nu0 nu1) nu2) (min (min mu0 mu1) mu2)) 1, lt_min hVpos one_pos, ?_⟩
  intro p d hd hν pt hs hsS hη
  obtain ⟨s, q, η⟩ := pt
  have hs' : 0 < s := hs
  have hsS' : s < p.ε ^ (-bexp) := hsS
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν' : p.ν ≤ min (min (min nu0 nu1) nu2) (min (min mu0 mu1) mu2) :=
    le_trans hν (min_le_left _ _)
  simp only [le_min_iff] at hν'
  obtain ⟨⟨⟨e_nu0, e_nu1⟩, e_nu2⟩, ⟨⟨e_mu0, e_mu1⟩, e_mu2⟩⟩ := hν'
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
  have hS0 : 0 ≤ S := by linarith
  have hSK : S ≤ Real.exp (bexp * max dp 0 / p.ν) := by
    rw [hSeq]
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hνpos.le
    exact mul_le_mul_of_nonneg_left (le_max_of_le_left hd.le_dp) hb.le
  have hε1 : p.ε ≤ 1 := by
    rw [hd.eps_eq]
    apply Real.exp_le_one_iff.2
    rw [neg_div]
    exact neg_nonpos.2 (div_nonneg hdnn hνpos.le)
  rw [hd.c_eq] at hη
  have hX0 : 0 ≤ (p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1 := by
    have h1 : 0 ≤ (p.ν ^ 2)⁻¹ / p.ν := by positivity
    have h2 := Real.sqrt_nonneg S
    linarith
  have hthr : max (max Cq0 Cq1) Cq2 * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) < |η| := hη
  have t0 : Cq0 * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) < |η| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left Cq0 Cq1) (le_max_left _ Cq2)) hX0) hthr
  have t1 : Cq1 * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) < |η| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right Cq0 Cq1) (le_max_left _ Cq2)) hX0) hthr
  have t2 : Cq2 * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) < |η| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ Cq2) hX0) hthr
  obtain ⟨hl0, hb0'⟩ := hK0 p.ν hνpos e_mu0 S hS1 hSK η t0
  obtain ⟨hl1, hb1'⟩ := hK1 p.ν hνpos e_mu1 S hS1 hSK η t1
  obtain ⟨hl2, hb2'⟩ := hK2 p.ν hνpos e_mu2 S hS1 hSK η t2
  -- the three jets of the train at the point
  have hzf : ∀ C' : ℝ, C' / p.ν + 2 + (|η| - C' / p.ν - 2) ≤ |(q, η).2| := by
    intro C'
    show C' / p.ν + 2 + (|η| - C' / p.ν - 2) ≤ |η|
    linarith
  have hψ0 := hT0 p.ν hνpos e_nu0 p.c hpc p.train hd.train_buc S hS0
    (|η| - C'0 / p.ν - 2) (by linarith) s hs' hsS'.le (q, η) (hzf C'0)
  have hψ1 := hT1 p.ν hνpos e_nu1 p.c hpc p.train hd.train_buc S hS0
    (|η| - C'1 / p.ν - 2) (by linarith) s hs' hsS'.le (q, η) (hzf C'1)
  have hψ2 := hT2 p.ν hνpos e_nu2 p.c hpc p.train hd.train_buc S hS0
    (|η| - C'2 / p.ν - 2) (by linarith) s hs' hsS'.le (q, η) (hzf C'2)
  dsimp only at hψ0 hψ1 hψ2
  obtain ⟨hA0, -, -, -⟩ := hψ0
  obtain ⟨hA1, -, -, -⟩ := hψ1
  obtain ⟨hA2, -, -, -⟩ := hψ2
  rw [T23RS.K_eq C0 N0 p.ν p.c S b0 _ C₀0 hd.c_eq] at hA0
  rw [T23RS.K_eq C1 N1 p.ν p.c S b1 _ C₀1 hd.c_eq] at hA1
  rw [T23RS.K_eq C2 N2 p.ν p.c S b2 _ C₀2 hd.c_eq] at hA2
  have hW := T23Tail.transWeight_le_jap hmZ0 hs'.le q η
  have hWn := T23Tail.transWeight_nonneg mZ (s, (q, η))
  have hsq : Real.sqrt s ≤ 1 + S := T23RS.sqrt_le_one_add hsS'.le hS0
  have ha : Real.sqrt s * transWeight mZ (s, (q, η)) ≤ (1 + S) * (1 + η ^ 2) ^ ⌈mZ / 2⌉₊ :=
    mul_le_mul hsq hW hWn (by linarith)
  -- term 0: the value `ψ`
  have T0 : Real.sqrt s * transWeight mZ (s, (q, η)) *
      ‖UnforcedLeray.Short.PartI.ageJet 0 0 p.train.ψ s (q, η)‖ ≤
        Real.exp (-(D + 2) / p.ν) / 2 := by
    have hh := mul_le_mul ha hA0 (norm_nonneg _) (mul_nonneg (by linarith) (by positivity))
    rw [pow_one] at hb0'
    exact hh.trans hb0'
  -- term 1: the derivative `∂_η ψ`, with `|η| ≤ 1 + η²`
  have hη1 : |η| ≤ 1 + η ^ 2 := T23RS.abs_le_one_add_sq η
  have hWη : transWeight mZ (s, (q, η)) * |η| ≤ (1 + η ^ 2) ^ (⌈mZ / 2⌉₊ + 1) := by
    rw [pow_succ]
    exact mul_le_mul hW hη1 (abs_nonneg η) (by positivity)
  have T1 : Real.sqrt s * transWeight mZ (s, (q, η)) *
      (|η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.ψ s (q, η)‖) ≤
        Real.exp (-(D + 2) / p.ν) / 2 := by
    have hh : Real.sqrt s * transWeight mZ (s, (q, η)) *
        (|η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.ψ s (q, η)‖) ≤
        (1 + S) * (1 + η ^ 2) ^ (⌈mZ / 2⌉₊ + 1) *
          (UnforcedLeray.Short.PartI.polyPS C1 N1 p.ν (p.ν ^ 2)⁻¹ S *
            (Real.exp (-(b1 * (|η| - C'1 / p.ν - 2) / (p.ν ^ 2)⁻¹)) +
              Real.exp (-(b1 * (|η| - C'1 / p.ν - 2) ^ 2 / (C₀1 + p.ν * S))))) := by
      calc Real.sqrt s * transWeight mZ (s, (q, η)) *
            (|η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.ψ s (q, η)‖)
          = Real.sqrt s * (transWeight mZ (s, (q, η)) * |η|) *
              ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.ψ s (q, η)‖ := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul hsq hWη (mul_nonneg hWn (abs_nonneg η)) (by linarith))
            hA1 (norm_nonneg _) (mul_nonneg (by linarith) (by positivity))
    rw [pow_one] at hb1'
    exact hh.trans hb1'
  -- term 2: the derivative `∂_s ψ`, with `2s ≤ 2(1+S)`
  have T2 : Real.sqrt s * transWeight mZ (s, (q, η)) *
      (2 * s * ‖UnforcedLeray.Short.PartI.ageJet 1 0 p.train.ψ s (q, η)‖) ≤
        Real.exp (-(D + 2) / p.ν) / 2 := by
    have h2sA : 2 * s * ‖UnforcedLeray.Short.PartI.ageJet 1 0 p.train.ψ s (q, η)‖ ≤
        2 * (1 + S) * (UnforcedLeray.Short.PartI.polyPS C2 N2 p.ν (p.ν ^ 2)⁻¹ S *
            (Real.exp (-(b2 * (|η| - C'2 / p.ν - 2) / (p.ν ^ 2)⁻¹)) +
              Real.exp (-(b2 * (|η| - C'2 / p.ν - 2) ^ 2 / (C₀2 + p.ν * S))))) :=
      mul_le_mul (by linarith) hA2 (norm_nonneg _) (by linarith)
    have hh := mul_le_mul ha h2sA (mul_nonneg (by linarith) (norm_nonneg _))
      (mul_nonneg (by linarith) (by positivity))
    rw [← T23RS.polyPS_two] at hb2'
    refine le_trans (le_of_le_of_eq hh ?_) hb2'
    ring
  -- assembling
  have hH := T23Tail.abs_raisedStream_le p.train hs' q η
  have hX : Real.sqrt s * transWeight mZ (s, (q, η)) *
        ‖UnforcedLeray.Short.PartI.ageJet 0 0 p.train.ψ s (q, η)‖ +
      Real.sqrt s * transWeight mZ (s, (q, η)) *
        (|η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.ψ s (q, η)‖) +
      Real.sqrt s * transWeight mZ (s, (q, η)) *
        (2 * s * ‖UnforcedLeray.Short.PartI.ageJet 1 0 p.train.ψ s (q, η)‖) ≤
        3 / 2 * Real.exp (-(D + 2) / p.ν) := by
    linarith
  have hnn : 0 ≤ Real.sqrt s * transWeight mZ (s, (q, η)) := mul_nonneg (Real.sqrt_nonneg _) hWn
  have h1 : Real.sqrt s * transWeight mZ (s, (q, η)) *
      |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η| ≤
      Real.sqrt s * transWeight mZ (s, (q, η)) *
        ‖UnforcedLeray.Short.PartI.ageJet 0 0 p.train.ψ s (q, η)‖ +
      Real.sqrt s * transWeight mZ (s, (q, η)) *
        (|η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.ψ s (q, η)‖) +
      Real.sqrt s * transWeight mZ (s, (q, η)) *
        (2 * s * ‖UnforcedLeray.Short.PartI.ageJet 1 0 p.train.ψ s (q, η)‖) := by
    refine le_trans (mul_le_mul_of_nonneg_left hH hnn) (le_of_eq ?_)
    ring
  have hnum := T23RS.three_half_le (D := D) hνpos hν1
  show Real.sqrt s * transWeight mZ (s, (q, η)) *
      (p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η|) ≤ Real.exp (-D / p.ν) / 2
  calc Real.sqrt s * transWeight mZ (s, (q, η)) *
        (p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η|)
      = p.ε * (Real.sqrt s * transWeight mZ (s, (q, η)) *
          |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η|) := by ring
    _ ≤ 1 * (Real.sqrt s * transWeight mZ (s, (q, η)) *
          ‖UnforcedLeray.Short.PartI.ageJet 0 0 p.train.ψ s (q, η)‖ +
        Real.sqrt s * transWeight mZ (s, (q, η)) *
          (|η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.ψ s (q, η)‖) +
        Real.sqrt s * transWeight mZ (s, (q, η)) *
          (2 * s * ‖UnforcedLeray.Short.PartI.ageJet 1 0 p.train.ψ s (q, η)‖)) :=
        mul_le_mul hε1 h1 (mul_nonneg hnn (abs_nonneg _)) zero_le_one
    _ = _ := one_mul _
    _ ≤ 3 / 2 * Real.exp (-(D + 2) / p.ν) := hX
    _ ≤ Real.exp (-D / p.ν) / 2 := hnum

end UnforcedLeray.Short.IIIa
