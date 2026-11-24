import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.Leaves
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.RawProfJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Velocity
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4

/-!
# Part II-b, task `PartII-b:G3/2`: the leaf `RawCoeffWindowTail`

Source of record: `the November 2 reference manuscript` (SP), lines 463-467
(`sct:transverse`), 2419-2423 (raw coefficients `b_raw = (v₁, v₂ + εH)`), 2447-2455
("Increasing `C_D` makes all required coefficient tails at most `e^{-D/ν}`; fixed weights and `K`
derivatives change only the polynomial cost").

Proof: `chartJet b_raw ≤ chartJet v + chartJet (He_z)` (`rawProf_eq`, `chartJet_add_smul`); the
velocity part is bounded by the jets `(0,0), (1,0), (0,1)` of `v` (`TrainChartBridge`), the raised
part by the six jets `ℓ + j ≤ 2` of `ψ` (`RaisedChartBridge`); every jet is absorbed, with the weight
`(1+S)³(1+η²)`, by `sct:transverse` and `tailAbsorb` at `D + 1`, and `123 e^{-(D+1)/ν} ≤ e^{-D/ν}`
for `ν ≤ 1/180`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartI UnforcedLeray.Short.IIIa

namespace RawCoeffTail

/-- `sct:transverse` in the uniform form, from the Part I tasks (as
`trainTransverseTailsUniform_uncond`). -/
theorem tailsUniform : TrainTransverseTailsUniform := by
  have hFD0 : OverlapFluctuationDecay := overlap_fluctuation_decay overlap_highnorm_uniform
  have hOv : TrainOverlap :=
    trainOverlap_proof hFD0
      (overlap_mean_decay overlap_highnorm_uniform hFD0 overlap_mean_primitive)
  have hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  have hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  exact trainTransverseTailsUniform_of (trainTransverseTails_proof hVort hTails)

/-- The jets `(ℓ, j)` of `ψ` and `v` on the exterior slab, with the weight `(1+S)³(1+η²)`. -/
theorem jetTail (ℓ j : ℕ) (D b dm dp : ℝ) (hD : 0 < D) (hb : 0 < b) :
    ∃ C_D₀ ν₀ : ℝ, 1 ≤ C_D₀ ∧ 0 < ν₀ ∧
      ∀ C_D : ℝ, C_D₀ ≤ C_D →
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        ∀ x : Coord, 0 < x.1 → x.1 ≤ p.ε ^ (-b) →
          C_D * (p.c / p.ν + Real.sqrt (p.ε ^ (-b)) + 1) < |x.2.2| →
          (1 + p.ε ^ (-b)) ^ 3 * (1 + x.2.2 ^ 2) * ‖ageJet ℓ j p.train.ψ x.1 x.2‖ ≤
              Real.exp (-D / p.ν) / 2 ∧
            (1 + p.ε ^ (-b)) ^ 3 * (1 + x.2.2 ^ 2) * ‖ageJet ℓ j p.train.v x.1 x.2‖ ≤
              Real.exp (-D / p.ν) / 2 := by
  obtain ⟨b₀, C₀, C', C, N, ν₁, hb₀, hC₀, _hC', _hC, hν₁, hT'⟩ := tailsUniform 2 (by norm_num) ℓ j
  have hKn : 0 ≤ b * max dp 0 := mul_nonneg hb.le (le_max_right _ _)
  obtain ⟨Cp, ν₂, _hCp, hν₂, hK'⟩ :=
    tailAbsorb b₀ C₀ C' C (b * max dp 0) D N 3 1 hb₀ hC₀ hD hKn
  refine ⟨max Cp 1, min ν₁ ν₂, le_max_right Cp 1, lt_min hν₁ hν₂, ?_⟩
  intro C_D hCD p d hd hν x hx0 hxS hη
  set S : ℝ := p.ε ^ (-b) with hS_def
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hpc : p.c = trainPeriod 2 p.ν := by
    rw [hd.c_eq]
    unfold trainPeriod
    rw [Real.rpow_neg p.ν_pos.le, Real.rpow_two]
  have hdnn : 0 ≤ d := le_trans hd.dm_pos.le hd.dm_le
  have hSeq : S = Real.exp (b * d / p.ν) := by
    rw [hS_def, Real.rpow_def_of_pos p.ε_pos, hd.eps_eq, Real.log_exp]
    congr 1
    ring
  have hS1 : 1 ≤ S := by
    rw [hSeq]
    exact Real.one_le_exp (div_nonneg (mul_nonneg hb.le hdnn) hνpos.le)
  have hSK : S ≤ Real.exp (b * max dp 0 / p.ν) := by
    rw [hSeq]
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hνpos.le
    exact mul_le_mul_of_nonneg_left (le_max_of_le_left hd.le_dp) hb.le
  have hW_nonneg : 0 ≤ (p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1 := by positivity
  have hCp_le : Cp ≤ C_D := (le_max_left Cp 1).trans hCD
  have hthr : Cp * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) < |x.2.2| := by
    have hL_eq : C_D * (p.c / p.ν + Real.sqrt S + 1) =
        C_D * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) := by
      rw [hd.c_eq]
    calc Cp * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1)
        ≤ C_D * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) :=
          mul_le_mul_of_nonneg_right hCp_le hW_nonneg
      _ = C_D * (p.c / p.ν + Real.sqrt S + 1) := hL_eq.symm
      _ < |x.2.2| := hη
  obtain ⟨hl, hmain⟩ := hK' p.ν hνpos hν2 S hS1 hSK x.2.2 hthr
  have hlpos : 0 ≤ |x.2.2| - C' / p.ν - 2 := by linarith
  have hT2 := hT' p.ν hνpos hν1 p.c hpc p.train hd.train_buc S (by linarith)
    (|x.2.2| - C' / p.ν - 2) hlpos x.1 hx0 hxS x.2
    (by show C' / p.ν + 2 + (|x.2.2| - C' / p.ν - 2) ≤ |x.2.2|; linarith)
  dsimp only at hT2
  obtain ⟨hψ, hv, _, _⟩ := hT2
  rw [T23RS.K_eq C N p.ν p.c S b₀ (|x.2.2| - C' / p.ν - 2) C₀ hd.c_eq] at hψ hv
  rw [pow_one] at hmain
  have hWpos : 0 ≤ (1 + S) ^ 3 * (1 + x.2.2 ^ 2) := by positivity
  exact ⟨(mul_le_mul_of_nonneg_left hψ hWpos).trans hmain,
    (mul_le_mul_of_nonneg_left hv hWpos).trans hmain⟩

/-- The weights: with `1 ≤ A = 1 + s ≤ B = 1 + S` and `T = 1 + η²`. -/
theorem weights {s S t : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) (ht : 0 ≤ t) :
    (1 + s) ≤ (1 + S) ^ 3 * (1 + t ^ 2) ∧
    (1 + s) * (2 + t) ≤ 3 * ((1 + S) ^ 3 * (1 + t ^ 2)) ∧
    (1 + s) * (2 * s) ≤ 2 * ((1 + S) ^ 3 * (1 + t ^ 2)) ∧
    (1 + s) * (20 * (1 + t + s) ^ 2) ≤ 40 * ((1 + S) ^ 3 * (1 + t ^ 2)) := by
  set A : ℝ := 1 + s with hA
  set B : ℝ := 1 + S with hB
  set T : ℝ := 1 + t ^ 2 with hT
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  have hAB : A ≤ B := by rw [hA, hB]; linarith
  have hB1 : 1 ≤ B := hA1.trans hAB
  have hT1 : 1 ≤ T := by rw [hT]; nlinarith
  have hB3 : B ≤ B ^ 3 := le_self_pow₀ hB1 (by norm_num)
  have hA3 : A ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (by linarith) hAB 3
  have hAB3 : A ≤ B ^ 3 := hAB.trans hB3
  have hB3pos : 0 ≤ B ^ 3 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc A ≤ B ^ 3 := hAB3
      _ = B ^ 3 * 1 := (mul_one _).symm
      _ ≤ B ^ 3 * T := mul_le_mul_of_nonneg_left hT1 hB3pos
  · have h2t : 2 + t ≤ 3 * T := by rw [hT]; nlinarith
    calc A * (2 + t) ≤ B ^ 3 * (3 * T) :=
          mul_le_mul hAB3 h2t (by linarith) hB3pos
      _ = 3 * (B ^ 3 * T) := by ring
  · have hA2 : A * A ≤ B ^ 3 := by nlinarith
    calc A * (2 * s) ≤ A * (2 * A) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [hA]; linarith
      _ = 2 * (A * A) := by ring
      _ ≤ 2 * (B ^ 3 * 1) := by nlinarith
      _ ≤ 2 * (B ^ 3 * T) := by nlinarith
  · have h1 : 1 + t + s ≤ A * (1 + t) := by rw [hA]; nlinarith [mul_nonneg hs ht]
    have h2 : (1 + t) ^ 2 ≤ 2 * T := by rw [hT]; nlinarith [sq_nonneg (1 - t)]
    have h3 : (1 + t + s) ^ 2 ≤ A ^ 2 * (2 * T) := by
      calc (1 + t + s) ^ 2 ≤ (A * (1 + t)) ^ 2 :=
            pow_le_pow_left₀ (by linarith) h1 2
        _ = A ^ 2 * (1 + t) ^ 2 := by ring
        _ ≤ A ^ 2 * (2 * T) := mul_le_mul_of_nonneg_left h2 (by positivity)
    calc A * (20 * (1 + t + s) ^ 2) ≤ A * (20 * (A ^ 2 * (2 * T))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
      _ = 40 * (A ^ 3 * T) := by ring
      _ ≤ 40 * (B ^ 3 * T) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hA3 (by linarith)

end RawCoeffTail

open RawCoeffTail RawProfJetHelp in
/-- **`RawCoeffWindowTail`** (SP 463-467, 2419-2423, 2447-2455). -/
theorem rawCoeffWindowTail_proof : RawCoeffWindowTail := by
  intro D hD a b _ha hb dm dp _hdm
  have hD' : 0 < D + 1 := by linarith
  obtain ⟨C0, n0, hC0, hn0, H0⟩ := jetTail 0 0 (D + 1) b dm dp hD' hb
  obtain ⟨C1, n1, _hC1, hn1, H1⟩ := jetTail 1 0 (D + 1) b dm dp hD' hb
  obtain ⟨C2, n2, _hC2, hn2, H2⟩ := jetTail 0 1 (D + 1) b dm dp hD' hb
  obtain ⟨C3, n3, _hC3, hn3, H3⟩ := jetTail 2 0 (D + 1) b dm dp hD' hb
  obtain ⟨C4, n4, _hC4, hn4, H4⟩ := jetTail 1 1 (D + 1) b dm dp hD' hb
  obtain ⟨C5, n5, _hC5, hn5, H5⟩ := jetTail 0 2 (D + 1) b dm dp hD' hb
  have hBridge : TrainChartBridge := trainChartBridge_of trainVelSmooth_proof
  set CD : ℝ := max C0 (max C1 (max C2 (max C3 (max C4 C5))))
  set n : ℝ := min (min n0 (min n1 (min n2 (min n3 (min n4 n5))))) (1 / 180)
  have hn : 0 < n := lt_min (lt_min hn0 (lt_min hn1 (lt_min hn2 (lt_min hn3 (lt_min hn4 hn5)))))
    (by norm_num)
  refine ⟨CD, n, hC0.trans (le_max_left _ _), hn, ?_⟩
  intro C_D hCD p d hreg hν x hx
  rcases hx with ⟨⟨hxσ, hxS⟩, hη⟩
  have hx0 : 0 < x.1 := lt_of_lt_of_le (Real.rpow_pos_of_pos p.ε_pos a) hxσ
  have hνpos : 0 < p.ν := p.ν_pos
  -- thresholds
  have hCi : C0 ≤ C_D ∧ C1 ≤ C_D ∧ C2 ≤ C_D ∧ C3 ≤ C_D ∧ C4 ≤ C_D ∧ C5 ≤ C_D := by
    refine ⟨(le_max_left _ _).trans hCD, ((le_max_left _ _).trans (le_max_right _ _)).trans hCD,
      ?_, ?_, ?_, ?_⟩
    · exact ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hCD
    · exact ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))).trans hCD
    · exact ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))).trans hCD
    · exact ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))).trans hCD
  have hνi : p.ν ≤ n0 ∧ p.ν ≤ n1 ∧ p.ν ≤ n2 ∧ p.ν ≤ n3 ∧ p.ν ≤ n4 ∧ p.ν ≤ n5 ∧
      p.ν ≤ 1 / 180 := by
    have h := hν
    have hm := min_le_left (min n0 (min n1 (min n2 (min n3 (min n4 n5))))) (1 / 180)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.trans (min_le_right _ _)⟩
    · exact h.trans (hm.trans (min_le_left _ _))
    · exact h.trans (hm.trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact h.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
    · exact h.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
    · exact h.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    · exact h.trans (hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
  obtain ⟨hC0', hC1', hC2', hC3', hC4', hC5'⟩ := hCi
  obtain ⟨hn0', hn1', hn2', hn3', hn4', hn5', hn180⟩ := hνi
  obtain ⟨j00ψ, j00v⟩ := H0 C_D hC0' p d hreg hn0' x hx0 hxS hη
  obtain ⟨j10ψ, j10v⟩ := H1 C_D hC1' p d hreg hn1' x hx0 hxS hη
  obtain ⟨j01ψ, j01v⟩ := H2 C_D hC2' p d hreg hn2' x hx0 hxS hη
  obtain ⟨j20ψ, -⟩ := H3 C_D hC3' p d hreg hn3' x hx0 hxS hη
  obtain ⟨j11ψ, -⟩ := H4 C_D hC4' p d hreg hn4' x hx0 hxS hη
  obtain ⟨j02ψ, -⟩ := H5 C_D hC5' p d hreg hn5' x hx0 hxS hη
  set S : ℝ := p.ε ^ (-b)
  set W : ℝ := (1 + S) ^ 3 * (1 + x.2.2 ^ 2) with hW
  set e' : ℝ := Real.exp (-(D + 1) / p.ν)
  -- the jet decomposition of `b_raw`
  obtain ⟨hTd, hRd⟩ := trainDiff p d dm dp hreg x hx0
  have hd0 : 0 ≤ d := le_trans hreg.dm_pos.le hreg.dm_le
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg hd0 hνpos.le)
  have hsplit : chartJet (rawProf p) x ≤ chartJet (trainProf p) x + chartJet (raisedMerid p) x := by
    rw [rawProf_eq]
    exact chartJet_add_smul hε0 hε1 x hTd hRd
  have hJr : chartJet (raisedMerid p) x =
      |raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x|
        + |kAge (raisedProf p) x| := chartJet_smul_m1 x hRd
  have hRB := raisedChartBridge_proof p d dm dp hreg x hx0
  obtain ⟨hb_v, hb_s, hb_q, hb_η⟩ := hBridge p d dm dp hreg x hx0
  have hkv : ‖kAge (trainProf p) x‖ ≤
      2 * x.1 * ‖Axi.dS (trainProf p) x‖ + |x.2.2| * ‖Axi.dEta (trainProf p) x‖ := by
    unfold kAge
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_eq_abs]
  have hJt : chartJet (trainProf p) x ≤
      ‖ageJet 0 0 p.train.v x.1 x.2‖ + (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖ +
        2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖ := by
    unfold chartJet
    have h1 : 2 * x.1 * ‖Axi.dS (trainProf p) x‖ ≤ 2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖ :=
      mul_le_mul_of_nonneg_left hb_s (by linarith)
    have h2 : |x.2.2| * ‖Axi.dEta (trainProf p) x‖ ≤ |x.2.2| * ‖ageJet 0 1 p.train.v x.1 x.2‖ :=
      mul_le_mul_of_nonneg_left hb_η (abs_nonneg _)
    linarith [h1, h2, hkv, hb_v, hb_q, hb_η]
  -- the weights
  have hS0 : 0 ≤ S := (Real.rpow_pos_of_pos p.ε_pos (-b)).le
  have ht0 : 0 ≤ |x.2.2| := abs_nonneg _
  have hsq : x.2.2 ^ 2 = |x.2.2| ^ 2 := (sq_abs _).symm
  obtain ⟨w1, w2, w3, w4⟩ := weights hx0.le hxS ht0
  rw [← hsq] at w1 w2 w3 w4
  -- the jets
  set Spsi : ℝ := ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
    ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
    ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + ‖ageJet 0 2 p.train.ψ x.1 x.2‖ with hSpsi
  have hWS : W * Spsi ≤ 6 * (e' / 2) := by
    rw [hSpsi]
    calc W * (‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + ‖ageJet 0 2 p.train.ψ x.1 x.2‖)
        = W * ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + W * ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
          W * ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + W * ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
          W * ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + W * ‖ageJet 0 2 p.train.ψ x.1 x.2‖ := by ring
      _ ≤ e' / 2 + e' / 2 + e' / 2 + e' / 2 + e' / 2 + e' / 2 := by
        gcongr
      _ = 6 * (e' / 2) := by ring
  have hRB' : |raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x| +
      |kAge (raisedProf p) x| ≤ 20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi := hRB
  have hSpsi0 : 0 ≤ Spsi := by rw [hSpsi]; positivity
  have hA0 : 0 ≤ 1 + x.1 := by linarith
  have hmain : (1 + x.1) * chartJet (rawProf p) x ≤ 123 * e' := by
    have hJ : chartJet (rawProf p) x ≤
        (‖ageJet 0 0 p.train.v x.1 x.2‖ + (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖ +
          2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) + 20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi := by
      rw [hJr] at hsplit
      linarith
    have e1 : (1 + x.1) * ‖ageJet 0 0 p.train.v x.1 x.2‖ ≤ e' / 2 :=
      (mul_le_mul_of_nonneg_right w1 (norm_nonneg _)).trans j00v
    have e2 : (1 + x.1) * ((2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖) ≤ 3 * (e' / 2) := by
      rw [← mul_assoc]
      calc (1 + x.1) * (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖
          ≤ 3 * W * ‖ageJet 0 1 p.train.v x.1 x.2‖ :=
            mul_le_mul_of_nonneg_right (by rw [hW]; linarith) (norm_nonneg _)
        _ = 3 * (W * ‖ageJet 0 1 p.train.v x.1 x.2‖) := by ring
        _ ≤ 3 * (e' / 2) := by linarith
    have e3 : (1 + x.1) * (2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) ≤ 2 * (e' / 2) := by
      calc (1 + x.1) * (2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖)
          = (1 + x.1) * (2 * x.1) * ‖ageJet 1 0 p.train.v x.1 x.2‖ := by ring
        _ ≤ 2 * W * ‖ageJet 1 0 p.train.v x.1 x.2‖ :=
            mul_le_mul_of_nonneg_right (by rw [hW]; linarith) (norm_nonneg _)
        _ = 2 * (W * ‖ageJet 1 0 p.train.v x.1 x.2‖) := by ring
        _ ≤ 2 * (e' / 2) := by linarith
    have e4 : (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi) ≤ 40 * (6 * (e' / 2)) := by
      calc (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi)
          = (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2) * Spsi := by ring
        _ ≤ 40 * W * Spsi := mul_le_mul_of_nonneg_right (by rw [hW]; linarith) hSpsi0
        _ = 40 * (W * Spsi) := by ring
        _ ≤ 40 * (6 * (e' / 2)) := by linarith
    calc (1 + x.1) * chartJet (rawProf p) x
        ≤ (1 + x.1) * ((‖ageJet 0 0 p.train.v x.1 x.2‖ +
            (2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖ +
            2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) + 20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi) :=
          mul_le_mul_of_nonneg_left hJ hA0
      _ = (1 + x.1) * ‖ageJet 0 0 p.train.v x.1 x.2‖ +
            (1 + x.1) * ((2 + |x.2.2|) * ‖ageJet 0 1 p.train.v x.1 x.2‖) +
            (1 + x.1) * (2 * x.1 * ‖ageJet 1 0 p.train.v x.1 x.2‖) +
            (1 + x.1) * (20 * (1 + |x.2.2| + x.1) ^ 2 * Spsi) := by ring
      _ ≤ e' / 2 + 3 * (e' / 2) + 2 * (e' / 2) + 40 * (6 * (e' / 2)) := by linarith
      _ = 123 * e' := by ring
  -- `123 e^{-(D+1)/ν} ≤ e^{-D/ν}` for `ν ≤ 1/180`
  have hexp : 123 * e' ≤ Real.exp (-D / p.ν) := by
    have hsplit' : e' = Real.exp (-D / p.ν) * Real.exp (-(1 / p.ν)) := by
      show Real.exp (-(D + 1) / p.ν) = _
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hbig : (180 : ℝ) ≤ 1 / p.ν := by
      rw [le_div_iff₀ hνpos]
      linarith [show 180 * p.ν ≤ 1 by linarith]
    have hexp1 : 123 * Real.exp (-(1 / p.ν)) ≤ 1 := by
      have h1 : 1 / p.ν + 1 ≤ Real.exp (1 / p.ν) := Real.add_one_le_exp _
      have h2 : Real.exp (-(1 / p.ν)) = (Real.exp (1 / p.ν))⁻¹ := Real.exp_neg _
      rw [h2]
      have hpos : 0 < Real.exp (1 / p.ν) := Real.exp_pos _
      rw [← div_eq_mul_inv, div_le_one hpos]
      linarith
    rw [hsplit']
    have hE0 : 0 ≤ Real.exp (-D / p.ν) := (Real.exp_pos _).le
    calc 123 * (Real.exp (-D / p.ν) * Real.exp (-(1 / p.ν)))
        = Real.exp (-D / p.ν) * (123 * Real.exp (-(1 / p.ν))) := by ring
      _ ≤ Real.exp (-D / p.ν) * 1 := mul_le_mul_of_nonneg_left hexp1 hE0
      _ = Real.exp (-D / p.ν) := mul_one _
  exact hmain.trans hexp

end UnforcedLeray.Short.IIb

end
