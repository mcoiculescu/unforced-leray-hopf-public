import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5
import UnforcedLeray.Short.PartIIb.Tasks.FlatInverse
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.FlatColumnReal
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Velocity
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.Leaves
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.RawCoeff
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T20
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKopYoungLateBounds.KOutChart

/-!
# Part II-b, task `PartII-b:G3/2`: Window transverse tail bound (`WindowTransverseTailBound`)

Source of record: `the November 2 reference manuscript`
(SP), lines 463–467 (`sct:transverse`) and 2447–2455.

## Main results proved in this file (zero `sorry`)

1. **`trainTransverseTailsUniform_uncond`**: unconditional proof of
   `UnforcedLeray.Short.IIIa.TrainTransverseTailsUniform` from the Part I overlap and tail theorems.
2. **`trainVel_windowExtSet_weighted_bound`**: on `windowExtSet σ S L` with `σ = p.ε ^ a`,
   `S = p.ε ^ (-b)`, and `L = C_D * (p.c / p.ν + Real.sqrt S + 1)` (`C_D ≥ C_D₀`), the weighted
   train velocity and meridional gradient satisfy
   `‖p.train.v x.1 x.2‖ * Real.sqrt x.1 ≤ Real.exp (-D / p.ν)`,
   `2 * ‖Axi.dQ (trainProf p) x‖ * x.1 ≤ Real.exp (-D / p.ν)`, and
   `2 * ‖Axi.dEta (trainProf p) x‖ * x.1 ≤ Real.exp (-D / p.ν)` via `TailAbsorb` and
   `TrainChartBridge`.
3. **`hpIndNorm_sub_le` and `hpIndNorm_le_of_restrict_toProf`**: subadditivity of `hpIndNorm` on
   `HpR c` and comparison with the restricted `eLpNorm` of `toProf c g`.
4. **`flatK0opWindowTransverseTailBound_proof : FlatK0opWindowTransverseTailBound`**: complete
   unconditional proof of the flat operator transverse tail bound on `windowExtSet σ S L` using
   `flat_graph_bound_bgp` (`PartII-b:T13`/`T14`), `F10K0Help.flatK_unique_ae`, and
   `eLpNorm_restrict_flatK_le`.
5. **`windowTransverseTailBound_of`**: conditional assembly of `WindowTransverseTailBound` from the
   physical operator exterior tail bound `PhysKopWindowTransverseTailBound` and the proved flat
   operator exterior tail bound `flatK0opWindowTransverseTailBound_proof`.
6. **`physKopWindowTransverseTailBound_of_leaves`**, **`windowTransverseTailBound_of_leaves`**:
   the physical half from the identification leaf `KOutChartAe` (the weak output of `IsKOut` is
   a.e. the chart formula `kOutChart`, `TransverseTail/Leaves.lean`) and the coefficient leaf
   `RawCoeffWindowTail`, with the graph bound `profileGraphPhys_proof` (`T10`).
7. **`windowTransverseTailBound_of_chartAe`**: the target from `KOutChartAe` alone
   (`RawCoeffWindowTail` is proved in `TransverseTail/RawCoeff.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartI UnforcedLeray.Short.IIIa

/-! ## 1. Unconditional transverse tail bounds on `windowExtSet σ S L` -/

/-- Unconditional proof of `TrainTransverseTailsUniform` from the Part I overlap and tail tasks. -/
theorem trainTransverseTailsUniform_uncond : TrainTransverseTailsUniform := by
  have hFD0 : OverlapFluctuationDecay := overlap_fluctuation_decay overlap_highnorm_uniform
  have hOv : TrainOverlap :=
    trainOverlap_proof hFD0
      (overlap_mean_decay overlap_highnorm_uniform hFD0 overlap_mean_primitive)
  have hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  have hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  exact trainTransverseTailsUniform_of (trainTransverseTails_proof hVort hTails)

/-- Single jet `(ℓ, j)` of the train velocity on `windowExtSet σ S L`: for any `D > 0` and
`b > 0`, choosing `C_D₀ ≥ 1` via `tailAbsorb` at `(M = 1, m = 0)` gives
`(1 + S) * ‖ageJet ℓ j p.train.v x.1 x.2‖ ≤ Real.exp (-D / p.ν) / 2` for every `C_D ≥ C_D₀` and
`x ∈ windowExtSet σ S L` (`S = p.ε ^ (-b)`, `L = C_D * (p.c / p.ν + Real.sqrt S + 1)`). -/
theorem velTail_windowExtSet_jet (ℓ j : ℕ) (D b dm dp : ℝ) (hD : 0 < D) (hb : 0 < b) :
    ∃ C_D₀ ν₀ : ℝ, 1 ≤ C_D₀ ∧ 0 < ν₀ ∧
      ∀ C_D : ℝ, C_D₀ ≤ C_D →
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        let S : ℝ := p.ε ^ (-b)
        let L : ℝ := C_D * (p.c / p.ν + Real.sqrt S + 1)
        ∀ x : Coord, 0 < x.1 → x.1 ≤ S → L < |x.2.2| →
          (1 + S) * ‖ageJet ℓ j p.train.v x.1 x.2‖ ≤ Real.exp (-D / p.ν) / 2 := by
  obtain ⟨b₀, C₀, C', C, N, ν₁, hb₀, hC₀, _hC', _hC, hν₁, hT'⟩ :=
    trainTransverseTailsUniform_uncond 2 (by norm_num) ℓ j
  have hKn : 0 ≤ b * max dp 0 := mul_nonneg hb.le (le_max_right _ _)
  obtain ⟨Cp, ν₂, _hCp, hν₂, hK'⟩ :=
    tailAbsorb b₀ C₀ C' C (b * max dp 0) D N 1 0 hb₀ hC₀ hD hKn
  refine ⟨max Cp 1, min ν₁ ν₂, le_max_right Cp 1, lt_min hν₁ hν₂, ?_⟩
  intro C_D hCD p d hd hν S L x hx0 hxS hη
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hpc : p.c = trainPeriod 2 p.ν := by
    rw [hd.c_eq]
    unfold trainPeriod
    rw [Real.rpow_neg p.ν_pos.le, Real.rpow_two]
  have hdnn : 0 ≤ d := le_trans hd.dm_pos.le hd.dm_le
  have hSeq : S = Real.exp (b * d / p.ν) := by
    change p.ε ^ (-b) = Real.exp (b * d / p.ν)
    rw [Real.rpow_def_of_pos p.ε_pos, hd.eps_eq, Real.log_exp]
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
    have hL_eq : L = C_D * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) := by
      dsimp [L]
      rw [hd.c_eq]
    calc Cp * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1)
        ≤ C_D * ((p.ν ^ 2)⁻¹ / p.ν + Real.sqrt S + 1) :=
          mul_le_mul_of_nonneg_right hCp_le hW_nonneg
      _ = L := hL_eq.symm
      _ < |x.2.2| := hη
  obtain ⟨hl, hmain⟩ := hK' p.ν hνpos hν2 S hS1 hSK x.2.2 hthr
  have hlpos : 0 ≤ |x.2.2| - C' / p.ν - 2 := by linarith
  have hT2 := hT' p.ν hνpos hν1 p.c hpc p.train hd.train_buc S (by linarith)
    (|x.2.2| - C' / p.ν - 2) hlpos x.1 hx0 hxS x.2
    (by show C' / p.ν + 2 + (|x.2.2| - C' / p.ν - 2) ≤ |x.2.2|; linarith)
  dsimp only at hT2
  obtain ⟨_, hv, _, _⟩ := hT2
  rw [T23RS.K_eq C N p.ν p.c S b₀ (|x.2.2| - C' / p.ν - 2) C₀ hd.c_eq] at hv
  rw [pow_one, pow_zero, mul_one] at hmain
  refine (mul_le_mul_of_nonneg_left hv (by linarith)).trans hmain

/-- On `windowExtSet σ S L` (`σ = p.ε ^ a`, `S = p.ε ^ (-b)`, `L = C_D * (p.c / p.ν + Real.sqrt S + 1)`),
the age-weighted train velocity and meridional chart derivatives are bounded by `Real.exp (-D / p.ν)`
for all `C_D ≥ C_D₀`. -/
theorem trainVel_windowExtSet_weighted_bound (D a b dm dp : ℝ) (hD : 0 < D) (hb : 0 < b) :
    ∃ C_D₀ ν₀ : ℝ, 1 ≤ C_D₀ ∧ 0 < ν₀ ∧
      ∀ C_D : ℝ, C_D₀ ≤ C_D →
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        let σ : ℝ := p.ε ^ a
        let S : ℝ := p.ε ^ (-b)
        let L : ℝ := C_D * (p.c / p.ν + Real.sqrt S + 1)
        ∀ x ∈ windowExtSet σ S L,
          ‖p.train.v x.1 x.2‖ * Real.sqrt x.1 ≤ Real.exp (-D / p.ν) ∧
          2 * ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ * x.1 ≤ Real.exp (-D / p.ν) ∧
          2 * ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ * x.1 ≤ Real.exp (-D / p.ν) := by
  obtain ⟨CD0, ν0, hCD0, hν0, hJ0⟩ := velTail_windowExtSet_jet 0 0 D b dm dp hD hb
  obtain ⟨CD1, ν1, _hCD1, hν1, hJ1⟩ := velTail_windowExtSet_jet 0 1 D b dm dp hD hb
  have hBridge : TrainChartBridge := trainChartBridge_of trainVelSmooth_proof
  refine ⟨max CD0 CD1, min ν0 ν1, hCD0.trans (le_max_left CD0 CD1), lt_min hν0 hν1, ?_⟩
  intro C_D hCD p d hreg hν σ S L x hx
  rcases hx with ⟨⟨hxσ, hxS⟩, hη⟩
  have hσ_pos : 0 < σ := Real.rpow_pos_of_pos p.ε_pos a
  have hx0 : 0 < x.1 := lt_of_lt_of_le hσ_pos hxσ
  have hS0 : 0 ≤ S := (Real.rpow_pos_of_pos p.ε_pos (-b)).le
  have hsqrt_le : Real.sqrt x.1 ≤ 1 + S := T23RS.sqrt_le_one_add hxS hS0
  have hx1_le : x.1 ≤ 1 + S := by linarith
  have hCD0_le : CD0 ≤ C_D := (le_max_left CD0 CD1).trans hCD
  have hCD1_le : CD1 ≤ C_D := (le_max_right CD0 CD1).trans hCD
  have hν0_le : p.ν ≤ ν0 := hν.trans (min_le_left _ _)
  have hν1_le : p.ν ≤ ν1 := hν.trans (min_le_right _ _)
  have hj0 := hJ0 C_D hCD0_le p d hreg hν0_le x hx0 hxS hη
  have hj1 := hJ1 C_D hCD1_le p d hreg hν1_le x hx0 hxS hη
  obtain ⟨hb_v, -, hb_q, hb_η⟩ := hBridge p d dm dp hreg x hx0
  have hv_le : ‖p.train.v x.1 x.2‖ ≤ ‖ageJet 0 0 p.train.v x.1 x.2‖ := hb_v
  have hq_le : ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ ≤
      ‖ageJet 0 1 p.train.v x.1 x.2‖ := hb_q
  have hη_le : ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ ≤
      ‖ageJet 0 1 p.train.v x.1 x.2‖ := hb_η
  have hE_pos : 0 < Real.exp (-D / p.ν) := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · calc ‖p.train.v x.1 x.2‖ * Real.sqrt x.1
        ≤ ‖ageJet 0 0 p.train.v x.1 x.2‖ * (1 + S) :=
          mul_le_mul hv_le hsqrt_le (Real.sqrt_nonneg _) (norm_nonneg _)
      _ = (1 + S) * ‖ageJet 0 0 p.train.v x.1 x.2‖ := mul_comm _ _
      _ ≤ Real.exp (-D / p.ν) / 2 := hj0
      _ ≤ Real.exp (-D / p.ν) := by linarith
  · calc 2 * ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ * x.1
        ≤ 2 * ‖ageJet 0 1 p.train.v x.1 x.2‖ * (1 + S) := by
          have h1 : 2 * ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ ≤
              2 * ‖ageJet 0 1 p.train.v x.1 x.2‖ := by linarith
          exact mul_le_mul h1 hx1_le hx0.le (by positivity)
      _ = 2 * ((1 + S) * ‖ageJet 0 1 p.train.v x.1 x.2‖) := by ring
      _ ≤ 2 * (Real.exp (-D / p.ν) / 2) := mul_le_mul_of_nonneg_left hj1 (by norm_num)
      _ = Real.exp (-D / p.ν) := by ring
  · calc 2 * ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ * x.1
        ≤ 2 * ‖ageJet 0 1 p.train.v x.1 x.2‖ * (1 + S) := by
          have h1 : 2 * ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ ≤
              2 * ‖ageJet 0 1 p.train.v x.1 x.2‖ := by linarith
          exact mul_le_mul h1 hx1_le hx0.le (by positivity)
      _ = 2 * ((1 + S) * ‖ageJet 0 1 p.train.v x.1 x.2‖) := by ring
      _ ≤ 2 * (Real.exp (-D / p.ν) / 2) := mul_le_mul_of_nonneg_left hj1 (by norm_num)
      _ = Real.exp (-D / p.ν) := by ring

/-! ## 2. Pointwise and restricted `eLpNorm` bounds for `flatK` and `hpIndNorm` helpers -/

/-- On `0 < x.1`, `flatK` can be written in terms of the meridional chart derivatives `Axi.dQ` and
`Axi.dEta` of `(s, z) ↦ tr.v s z`. -/
theorem flatK_eq_on_pos {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0 b0q b0η : CProf)
    {x : Coord} (hx : 0 < x.1) :
    flatK tr b0 b0q b0η x =
      x.1 • ((tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
        b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
        b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)) := by
  have hdiff : DifferentiableAt ℝ (fun m : Coord => tr.v m.1 m.2) x :=
    ((tr.isTrain.smooth_v.mono fun y (_hy : 0 < y.1) => ⟨_hy.le, trivial⟩).differentiableOn
      (by simp)).differentiableAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hx)
  have hQ : ∀ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => tr.v x.1 z j) x.2 (1, 0) =
      Axi.dQ (fun m : Coord => tr.v m.1 m.2) x j := fun j =>
    flatPartial_comp_eq (fun m : Coord => tr.v m.1 m.2) x hdiff j (1, 0)
  have hE : ∀ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => tr.v x.1 z j) x.2 (0, 1) =
      Axi.dEta (fun m : Coord => tr.v m.1 m.2) x j := fun j =>
    flatPartial_comp_eq (fun m : Coord => tr.v m.1 m.2) x hdiff j (0, 1)
  ext j
  simp only [flatK, liftM, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
    Complex.real_smul, smul_eq_mul]
  rw [hQ j, hE j]

/-- Norm of `sqrtS g x` for `0 ≤ x.1`. -/
theorem norm_sqrtS_of_nonneg (g : CProf) {x : Coord} (_hx : 0 ≤ x.1) :
    ‖sqrtS g x‖ = Real.sqrt x.1 * ‖g x‖ := by
  unfold sqrtS
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x.1)]

/-- Pointwise bound on `‖flatK tr b0 b0q b0η x‖` in terms of `‖sqrtS b0q x‖`, `‖sqrtS b0η x‖`,
and `‖b0 x‖` when `0 < x.1`. -/
theorem norm_flatK_le_of_vel_grad {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (b0 b0q b0η : CProf) {x : Coord} (hx : 0 < x.1) {V D : ℝ} (_hV0 : 0 ≤ V) (_hD0 : 0 ≤ D)
    (hV : ‖tr.v x.1 x.2‖ ≤ V)
    (hQ : ‖Axi.dQ (fun m : Coord => tr.v m.1 m.2) x‖ ≤ D)
    (hE : ‖Axi.dEta (fun m : Coord => tr.v m.1 m.2) x‖ ≤ D) :
    ‖flatK tr b0 b0q b0η x‖ ≤
      (V * Real.sqrt x.1) * ‖sqrtS b0q x‖ +
        (V * Real.sqrt x.1) * ‖sqrtS b0η x‖ +
        (2 * D * x.1) * ‖b0 x‖ := by
  have hs0 : 0 ≤ x.1 := hx.le
  have hv0 : |tr.v x.1 x.2 0| ≤ V := by
    have h := PiLp.norm_apply_le (tr.v x.1 x.2) 0
    rw [Real.norm_eq_abs] at h
    exact h.trans hV
  have hv1 : |tr.v x.1 x.2 1| ≤ V := by
    have h := PiLp.norm_apply_le (tr.v x.1 x.2) 1
    rw [Real.norm_eq_abs] at h
    exact h.trans hV
  have hb0 : ‖b0 x 0‖ ≤ ‖b0 x‖ := PiLp.norm_apply_le (b0 x) 0
  have hb1 : ‖b0 x 1‖ ≤ ‖b0 x‖ := PiLp.norm_apply_le (b0 x) 1
  have ht1 : ‖(tr.v x.1 x.2 0 : ℂ) • b0q x‖ ≤ V * ‖b0q x‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hv0 (norm_nonneg _)
  have ht2 : ‖(tr.v x.1 x.2 1 : ℂ) • b0η x‖ ≤ V * ‖b0η x‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hv1 (norm_nonneg _)
  have ht3 : ‖b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ ≤ ‖b0 x‖ * D := by
    rw [norm_smul, liftM_norm]
    exact mul_le_mul hb0 hQ (norm_nonneg _) (norm_nonneg _)
  have ht4 : ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ ≤ ‖b0 x‖ * D := by
    rw [norm_smul, liftM_norm]
    exact mul_le_mul hb1 hE (norm_nonneg _) (norm_nonneg _)
  have hsum : ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
      b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
      b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ ≤
      V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D := by
    calc _ ≤ ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
              b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ +
            ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ := norm_add_le _ _
      _ ≤ ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x‖ +
            ‖b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ +
            ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖(tr.v x.1 x.2 0 : ℂ) • b0q x‖ + ‖(tr.v x.1 x.2 1 : ℂ) • b0η x‖ +
            ‖b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ +
            ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ ≤ V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D := by linarith
  have hsq : Real.sqrt x.1 * Real.sqrt x.1 = x.1 := Real.mul_self_sqrt hs0
  rw [flatK_eq_on_pos tr b0 b0q b0η hx, norm_smul, Real.norm_of_nonneg hs0]
  calc x.1 * ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
        b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
        b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖
      ≤ x.1 * (V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D) :=
        mul_le_mul_of_nonneg_left hsum hs0
    _ = (V * Real.sqrt x.1) * (Real.sqrt x.1 * ‖b0q x‖) +
          (V * Real.sqrt x.1) * (Real.sqrt x.1 * ‖b0η x‖) +
          (2 * D * x.1) * ‖b0 x‖ := by
        calc x.1 * (V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D)
            = (Real.sqrt x.1 * Real.sqrt x.1) * V * ‖b0q x‖ +
                (Real.sqrt x.1 * Real.sqrt x.1) * V * ‖b0η x‖ +
                (2 * D * x.1) * ‖b0 x‖ := by
              rw [hsq]; ring
          _ = _ := by ring
    _ = (V * Real.sqrt x.1) * ‖sqrtS b0q x‖ +
          (V * Real.sqrt x.1) * ‖sqrtS b0η x‖ +
          (2 * D * x.1) * ‖b0 x‖ := by
        rw [norm_sqrtS_of_nonneg b0q hs0, norm_sqrtS_of_nonneg b0η hs0]

/-- Restricted `eLpNorm` bound for `flatK` on a measurable set `S` where
`‖flatK x‖ ≤ A₁ ‖sqrtS b0q x‖ + A₁ ‖sqrtS b0η x‖ + A₂ ‖b0 x‖` for `0 < x.1`. -/
theorem eLpNorm_restrict_flatK_le {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (b0 b0q b0η : CProf) (hb0 : InHr c bgp b0) (hq : InHr c bgp (sqrtS b0q))
    (hη : InHr c bgp (sqrtS b0η)) (S : Set Coord) (hS : MeasurableSet S)
    {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hpt : ∀ x ∈ S, 0 < x.1 →
      ‖flatK tr b0 b0q b0η x‖ ≤
        A₁ * ‖sqrtS b0q x‖ + A₁ * ‖sqrtS b0η x‖ + A₂ * ‖b0 x‖) :
    eLpNorm (flatK tr b0 b0q b0η) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S) ≤
      ENNReal.ofReal A₁ * (hNorm c bgp (sqrtS b0q) + hNorm c bgp (sqrtS b0η)) +
        ENNReal.ofReal A₂ * hNorm c bgp b0 := by
  have hp1 : 1 ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]
    norm_num [bgp]
  have hae_pos : ∀ᵐ x ∂(hMeas c bgp), 0 < x.1 :=
    (Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)).mono fun x hx => hx.1
  let fq : Coord → ℝ := fun x => A₁ • ‖sqrtS b0q x‖
  let fη : Coord → ℝ := fun x => A₁ • ‖sqrtS b0η x‖
  let fb : Coord → ℝ := fun x => A₂ • ‖b0 x‖
  have hfq_m : AEStronglyMeasurable fq (hMeas c bgp) := hq.meas.norm.const_smul A₁
  have hfη_m : AEStronglyMeasurable fη (hMeas c bgp) := hη.meas.norm.const_smul A₁
  have hfb_m : AEStronglyMeasurable fb (hMeas c bgp) := hb0.meas.norm.const_smul A₂
  have hae_res : ∀ᵐ x ∂((hMeas c bgp).restrict S),
      ‖flatK tr b0 b0q b0η x‖ ≤ ‖(fq + fη + fb) x‖ := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hae_pos] with x hxS hx0
    have hnn : 0 ≤ (fq + fη + fb) x := by
      change 0 ≤ A₁ * ‖sqrtS b0q x‖ + A₁ * ‖sqrtS b0η x‖ + A₂ * ‖b0 x‖
      positivity
    rw [Real.norm_of_nonneg hnn]
    exact hpt x hxS hx0
  have hmono1 : eLpNorm (flatK tr b0 b0q b0η) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S) ≤
      eLpNorm (fq + fη + fb) (ENNReal.ofReal bgp) (hMeas c bgp) :=
    (eLpNorm_mono_ae hae_res).trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hadd1 : eLpNorm (fq + fη + fb) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le (hfq_m.add hfη_m) hfb_m hp1
  have hadd2 : eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le hfq_m hfη_m hp1
  have hsmul_q : eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₁ * hNorm c bgp (sqrtS b0q) := by
    change eLpNorm (A₁ • fun x => ‖sqrtS b0q x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₁]
    rfl
  have hsmul_η : eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₁ * hNorm c bgp (sqrtS b0η) := by
    change eLpNorm (A₁ • fun x => ‖sqrtS b0η x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₁]
    rfl
  have hsmul_b : eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₂ * hNorm c bgp b0 := by
    change eLpNorm (A₂ • fun x => ‖b0 x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₂]
    rfl
  calc eLpNorm (flatK tr b0 b0q b0η) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S)
      ≤ eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) := hmono1.trans hadd1
    _ ≤ (eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp)) +
          eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) := add_le_add hadd2 le_rfl
    _ = ENNReal.ofReal A₁ * (hNorm c bgp (sqrtS b0q) + hNorm c bgp (sqrtS b0η)) +
          ENNReal.ofReal A₂ * hNorm c bgp b0 := by
        rw [hsmul_q, hsmul_η, hsmul_b, mul_add]

/-- The indicator `eLpNorm` of `g : HpR c` on a measurable set `E` equals the restricted `eLpNorm`
of `toProf c g`. -/
theorem eLpNorm_indicator_eq_restrict_toProf {c : ℝ} (hc : 0 < c) (E : Set Coord)
    (hE : MeasurableSet E) (g : HpR c) :
    eLpNorm (E.indicator (g : Coord → Axi.Merid)) (ENNReal.ofReal bgp) (hMeas c bgp) =
      eLpNorm (toProf c g) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict E) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hE]
  have hae : toProf c g =ᵐ[(hMeas c bgp).restrict E] fun x => liftM ((g : Coord → Axi.Merid) x) :=
    ae_restrict_of_ae (toProf_ae_eq hc g)
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun _ => (liftM_norm _).symm)

/-- Upper bound on `hpIndNorm c E g` from a restricted `eLpNorm` bound on `toProf c g`. -/
theorem hpIndNorm_le_of_restrict_toProf {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (E : Set Coord)
    (hE : MeasurableSet E) (g : HpR c)
    (hbd : eLpNorm (toProf c g) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict E) ≤
      ENNReal.ofReal M) :
    hpIndNorm c E g ≤ M := by
  unfold hpIndNorm
  rw [eLpNorm_indicator_eq_restrict_toProf hc E hE g, ← ENNReal.toReal_ofReal hM]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd

/-- Subadditivity of `hpIndNorm c E` on `HpR c` for any measurable set `E`. -/
theorem hpIndNorm_sub_le {c : ℝ} (E : Set Coord) (hE : MeasurableSet E) (g₁ g₂ : HpR c) :
    hpIndNorm c E (g₁ - g₂) ≤ hpIndNorm c E g₁ + hpIndNorm c E g₂ := by
  unfold hpIndNorm
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]; norm_num [bgp]
  have hae : E.indicator ((g₁ - g₂ : HpR c) : Coord → Axi.Merid) =ᵐ[hMeas c bgp]
      E.indicator (g₁ : Coord → Axi.Merid) - E.indicator (g₂ : Coord → Axi.Merid) := by
    filter_upwards [Lp.coeFn_sub g₁ g₂] with x hx
    rw [Pi.sub_apply]
    by_cases hxE : x ∈ E
    · simp only [Set.indicator_of_mem hxE]
      exact hx
    · simp [Set.indicator_of_notMem hxE]
  have hm1 : AEStronglyMeasurable (E.indicator (g₁ : Coord → Axi.Merid)) (hMeas c bgp) :=
    (Lp.aestronglyMeasurable g₁).indicator hE
  have hm2 : AEStronglyMeasurable (E.indicator (g₂ : Coord → Axi.Merid)) (hMeas c bgp) :=
    (Lp.aestronglyMeasurable g₂).indicator hE
  have hle : eLpNorm (E.indicator ((g₁ - g₂ : HpR c) : Coord → Axi.Merid))
      (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm (E.indicator (g₁ : Coord → Axi.Merid)) (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm (E.indicator (g₂ : Coord → Axi.Merid)) (ENNReal.ofReal bgp) (hMeas c bgp) := by
    rw [eLpNorm_congr_ae hae]
    exact eLpNorm_sub_le hm1 hm2 hp1
  have hlt1 : eLpNorm (E.indicator (g₁ : Coord → Axi.Merid))
      (ENNReal.ofReal bgp) (hMeas c bgp) < ⊤ := by
    refine lt_of_le_of_lt (eLpNorm_mono fun x => ?_) (Lp.eLpNorm_lt_top g₁)
    exact norm_indicator_le_norm_self (g₁ : Coord → Axi.Merid) x
  have hlt2 : eLpNorm (E.indicator (g₂ : Coord → Axi.Merid))
      (ENNReal.ofReal bgp) (hMeas c bgp) < ⊤ := by
    refine lt_of_le_of_lt (eLpNorm_mono fun x => ?_) (Lp.eLpNorm_lt_top g₂)
    exact norm_indicator_le_norm_self (g₂ : Coord → Axi.Merid) x
  rw [← ENNReal.toReal_add hlt1.ne hlt2.ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hlt1.ne, hlt2.ne⟩) hle

/-! ## 3. Flat operator transverse tail bound (`FlatK0opWindowTransverseTailBound`) -/

lemma vQ_zero_eq : vQ 0 = vQ0 := by
  funext x i
  fin_cases i <;> simp [vQ, vQ0]

lemma dQ_zero_eq : dQ 0 = dZero := by
  funext x
  simp [dQ, dZero]

/-- **Flat operator exterior transverse tail bound (`FlatK0opWindowTransverseTailBound`,
SP 463–467, 2447–2455)**: for every `D > 0`, `a, b > 0`, and `dm, dp` (`0 < dm`), there exist
`C_D₀ ≥ 1`, `C_tail₀ > 0`, `k_tail₀ : ℕ`, and `ν₀ > 0` such that for all `C_D ≥ C_D₀`, in
`BgRegime p d dm dp` with `p.ν ≤ ν₀`, any flat interaction operator `K0 : HpR p.c →L[ℝ] HpR p.c`
satisfying `IsK0op p K0` obeys
`hpIndNorm p.c (windowExtSet σ S L) (K0 f) ≤ C_tail₀ * (p.ν ^ k_tail₀)⁻¹ * Real.exp (-D / p.ν) * ‖f‖`
with `σ = p.ε ^ a`, `S = p.ε ^ (-b)`, and `L = C_D * (p.c / p.ν + Real.sqrt S + 1)`. -/
def FlatK0opWindowTransverseTailBound : Prop :=
  ∀ D : ℝ, 0 < D → ∀ a b : ℝ, 0 < a → 0 < b → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_D₀ C_tail₀ : ℝ) (k_tail₀ : ℕ) (ν₀ : ℝ), 1 ≤ C_D₀ ∧ 0 < C_tail₀ ∧ 0 < ν₀ ∧
      ∀ C_D : ℝ, C_D₀ ≤ C_D →
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ K0 : HpR p.c →L[ℝ] HpR p.c, IsK0op p K0 → ∀ f : HpR p.c,
        let σ : ℝ := p.ε ^ a
        let S : ℝ := p.ε ^ (-b)
        let L : ℝ := C_D * (p.c / p.ν + Real.sqrt S + 1)
        hpIndNorm p.c (windowExtSet σ S L) (K0 f) ≤
          C_tail₀ * (p.ν ^ k_tail₀)⁻¹ * Real.exp (-D / p.ν) * ‖f‖

/-- Complete unconditional proof of `FlatK0opWindowTransverseTailBound`. -/
theorem flatK0opWindowTransverseTailBound_proof : FlatK0opWindowTransverseTailBound := by
  intro D hD a b _ha hb dm dp _hdm
  obtain ⟨C_D₀, ν_v, hCD₀, hν_v, hVel⟩ := trainVel_windowExtSet_weighted_bound D a b dm dp hD hb
  obtain ⟨C_flat, hC_flat, hFlat⟩ := flat_graph_bound_bgp
  refine ⟨C_D₀, 2 * C_flat, 1, min ν_v 1, hCD₀, by positivity, lt_min hν_v one_pos, ?_⟩
  intro C_D hCD p d hreg hν K0 hK0 f σ S L
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hν_v_le : p.ν ≤ ν_v := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hF_inHr : InHr p.c bgp (toProf p.c f) := inHr_toProf hc_pos f
  obtain ⟨b0, gq0, gη0, hb0_cls, hb0_resp, hgq0, hgη0, hK0_ae⟩ := hK0 f
  obtain ⟨_Sb', Qb', Eb', _hS', hQ', hE', _hSi', hQi', hEi'⟩ := hb0_cls.deriv
  obtain ⟨Sb, Qb, Eb, _hSb, hQb, hEb, hGraph⟩ :=
    hFlat p.ν p.c hν_pos hc_pos (toProf p.c f) b0 hF_inHr hb0_cls hb0_resp
  rw [vQ_zero_eq, dQ_zero_eq] at hQb
  have hK0_eq_flatK : toProf p.c (K0 f) =ᵐ[hMeas p.c bgp] flatK p.train b0 Qb' Eb' :=
    hK0_ae.trans (F10K0Help.flatK_unique_ae hν_pos hc_pos p.train hF_inHr
      hb0_cls hb0_resp hgq0 hgη0 hb0_cls hb0_resp hQ' hE')
  have hQb_ae : sqrtS Qb' =ᵐ[hMeas p.c bgp] sqrtS Qb := by
    have hvol := GradBoundHelp.hasWeakVec_unique hQ' hQb
    filter_upwards [hMeasAe p.c bgp _ hc_pos hvol] with x hx
    simp only [sqrtS, hx]
  have hEb_ae : sqrtS Eb' =ᵐ[hMeas p.c bgp] sqrtS Eb := by
    have hvol := GradBoundHelp.hasWeakVec_unique hE' hEb
    filter_upwards [hMeasAe p.c bgp _ hc_pos hvol] with x hx
    simp only [sqrtS, hx]
  have hNorm_Qb : hNorm p.c bgp (sqrtS Qb') = hNorm p.c bgp (sqrtS Qb) :=
    eLpNorm_congr_ae hQb_ae
  have hNorm_Eb : hNorm p.c bgp (sqrtS Eb') = hNorm p.c bgp (sqrtS Eb) :=
    eLpNorm_congr_ae hEb_ae
  have hF_norm : hNorm p.c bgp (toProf p.c f) = ENNReal.ofReal ‖f‖ := by
    rw [hNorm_toProf hc_pos f, (ofReal_norm f).symm]
  have hν_le_sqrt : p.ν ≤ Real.sqrt p.ν := by
    calc p.ν = Real.sqrt p.ν * Real.sqrt p.ν := (Real.mul_self_sqrt hν_pos.le).symm
      _ ≤ 1 * Real.sqrt p.ν :=
          mul_le_mul_of_nonneg_right (by simpa using Real.sqrt_le_sqrt hν1) (Real.sqrt_nonneg _)
      _ = Real.sqrt p.ν := one_mul _
  have hν_inv_ge_one : 1 ≤ (p.ν ^ 1)⁻¹ := by
    rw [pow_one]
    exact one_le_inv₀ hν_pos |>.mpr hν1
  have hb0_norm_le :
      hNorm p.c bgp b0 ≤ ENNReal.ofReal (C_flat * (p.ν ^ 1)⁻¹ * ‖f‖) := by
    have h1 : hNorm p.c bgp b0 ≤ ENNReal.ofReal C_flat * hNorm p.c bgp (toProf p.c f) :=
      (le_self_add.trans le_self_add).trans hGraph
    rw [hF_norm, ← ENNReal.ofReal_mul hC_flat.le] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    calc C_flat * ‖f‖ = C_flat * 1 * ‖f‖ := by ring
      _ ≤ C_flat * (p.ν ^ 1)⁻¹ * ‖f‖ := by gcongr
  have hgrad_norm_le :
      hNorm p.c bgp (sqrtS Qb') + hNorm p.c bgp (sqrtS Eb') ≤
        ENNReal.ofReal (C_flat * (p.ν ^ 1)⁻¹ * ‖f‖) := by
    rw [hNorm_Qb, hNorm_Eb]
    have h1 : ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) ≤
        ENNReal.ofReal C_flat * ENNReal.ofReal ‖f‖ := by
      rw [← hF_norm]
      calc ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))
          ≤ ENNReal.ofReal (Real.sqrt p.ν) *
              (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := by
            gcongr
        _ ≤ hNorm p.c bgp b0 + hNorm p.c bgp Sb +
              ENNReal.ofReal (Real.sqrt p.ν) *
                (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := le_add_self
        _ ≤ ENNReal.ofReal C_flat * hNorm p.c bgp (toProf p.c f) := hGraph
    have h_inv_mul : ENNReal.ofReal p.ν⁻¹ * ENNReal.ofReal p.ν = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le), inv_mul_cancel₀ hν_pos.ne',
        ENNReal.ofReal_one]
    calc hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)
        = 1 * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := (one_mul _).symm
      _ = ENNReal.ofReal p.ν⁻¹ *
            (ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))) := by
          rw [← mul_assoc, h_inv_mul]
      _ ≤ ENNReal.ofReal p.ν⁻¹ * (ENNReal.ofReal C_flat * ENNReal.ofReal ‖f‖) := by
          gcongr
      _ = ENNReal.ofReal (C_flat * (p.ν ^ 1)⁻¹ * ‖f‖) := by
          rw [pow_one, ← ENNReal.ofReal_mul hC_flat.le,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le)]
          congr 1; ring
  set E_exp : ℝ := Real.exp (-D / p.ν)
  have hE_nonneg : 0 ≤ E_exp := (Real.exp_pos _).le
  have hpt : ∀ x ∈ windowExtSet σ S L, 0 < x.1 →
      ‖flatK p.train b0 Qb' Eb' x‖ ≤
        E_exp * ‖sqrtS Qb' x‖ + E_exp * ‖sqrtS Eb' x‖ + E_exp * ‖b0 x‖ := by
    intro x hx hx0
    obtain ⟨hV_w, hQ_w, hE_w⟩ := hVel C_D hCD p d hreg hν_v_le x hx
    set V : ℝ := ‖p.train.v x.1 x.2‖
    set D_g : ℝ := max ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖
      ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖
    have hV0 : 0 ≤ V := norm_nonneg _
    have hD0 : 0 ≤ D_g := le_trans (norm_nonneg _) (le_max_left _ _)
    have hDg_w : 2 * D_g * x.1 ≤ E_exp := by
      rcases max_choice ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖
        ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ with hmax | hmax
      · dsimp [D_g]; rw [hmax]; exact hQ_w
      · dsimp [D_g]; rw [hmax]; exact hE_w
    have hflat := norm_flatK_le_of_vel_grad p.train b0 Qb' Eb' hx0 hV0 hD0
      le_rfl (le_max_left _ _) (le_max_right _ _)
    refine hflat.trans ?_
    gcongr
  have hMeas_ext : MeasurableSet (windowExtSet σ S L) := measurableSet_windowExtSet σ S L
  have hRes_bd := eLpNorm_restrict_flatK_le hc_pos p.train b0 Qb' Eb'
    hb0_cls.inHr hQi' hEi' (windowExtSet σ S L) hMeas_ext hE_nonneg hE_nonneg hpt
  have hRes_toProf :
      eLpNorm (toProf p.c (K0 f)) (ENNReal.ofReal bgp)
          ((hMeas p.c bgp).restrict (windowExtSet σ S L)) ≤
        ENNReal.ofReal ((2 * C_flat) * (p.ν ^ 1)⁻¹ * E_exp * ‖f‖) := by
    rw [eLpNorm_congr_ae (ae_restrict_of_ae hK0_eq_flatK)]
    calc eLpNorm (flatK p.train b0 Qb' Eb') (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (windowExtSet σ S L))
        ≤ ENNReal.ofReal E_exp * (hNorm p.c bgp (sqrtS Qb') + hNorm p.c bgp (sqrtS Eb')) +
            ENNReal.ofReal E_exp * hNorm p.c bgp b0 := hRes_bd
      _ ≤ ENNReal.ofReal E_exp * ENNReal.ofReal (C_flat * (p.ν ^ 1)⁻¹ * ‖f‖) +
            ENNReal.ofReal E_exp * ENNReal.ofReal (C_flat * (p.ν ^ 1)⁻¹ * ‖f‖) := by
          gcongr
      _ = ENNReal.ofReal ((2 * C_flat) * (p.ν ^ 1)⁻¹ * E_exp * ‖f‖) := by
          rw [← ENNReal.ofReal_mul hE_nonneg, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  exact hpIndNorm_le_of_restrict_toProf hc_pos (by positivity) (windowExtSet σ S L)
    hMeas_ext (K0 f) hRes_toProf

/-! ## 4. Physical operator exterior tail bound and conditional assembly (`PartII-b:G3/2`) -/

/-- **Physical operator exterior transverse tail bound (`PhysKopWindowTransverseTailBound`,
SP 463–467, 2447–2455)**: for every `D > 0`, `a, b > 0`, and `dm, dp` (`0 < dm`), there exist
`C_D₁ ≥ 1`, `C_tail₁ > 0`, `k_tail₁ : ℕ`, and `ν₁ > 0` such that for all `C_D ≥ C_D₁`, in
`BgRegime p d dm dp` with `p.ν ≤ ν₁` and `p.period ≤ 1`, any physical interaction operator
`Ke : HpR p.c →L[ℝ] HpR p.c` satisfying `IsKop p Ke` obeys
`hpIndNorm p.c (windowExtSet σ S L) (Ke f) ≤ C_tail₁ * (p.ν ^ k_tail₁)⁻¹ * Real.exp (-D / p.ν) * ‖f‖`
with `σ = p.ε ^ a`, `S = p.ε ^ (-b)`, and `L = C_D * (p.c / p.ν + Real.sqrt S + 1)`. -/
def PhysKopWindowTransverseTailBound : Prop :=
  ∀ D : ℝ, 0 < D → ∀ a b : ℝ, 0 < a → 0 < b → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_D₁ C_tail₁ : ℝ) (k_tail₁ : ℕ) (ν₁ : ℝ), 1 ≤ C_D₁ ∧ 0 < C_tail₁ ∧ 0 < ν₁ ∧
      ∀ C_D : ℝ, C_D₁ ≤ C_D →
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₁ → p.period ≤ 1 →
      ∀ Ke : HpR p.c →L[ℝ] HpR p.c, IsKop p Ke → ∀ f : HpR p.c,
        let σ : ℝ := p.ε ^ a
        let S : ℝ := p.ε ^ (-b)
        let L : ℝ := C_D * (p.c / p.ν + Real.sqrt S + 1)
        hpIndNorm p.c (windowExtSet σ S L) (Ke f) ≤
          C_tail₁ * (p.ν ^ k_tail₁)⁻¹ * Real.exp (-D / p.ν) * ‖f‖

/-- **Conditional assembly of `WindowTransverseTailBound` (`PartII-b:G3/2`)** from
`PhysKopWindowTransverseTailBound` and the proved `flatK0opWindowTransverseTailBound_proof`. -/
theorem windowTransverseTailBound_of (hPhys : PhysKopWindowTransverseTailBound) :
    UnforcedLeray.Short.IIb.WindowTransverseTailBound := by
  intro D hD a b ha hb dm dp hdm
  obtain ⟨CD0, C0, k0, ν0, hCD0, hC0, hν0, hFlat⟩ :=
    flatK0opWindowTransverseTailBound_proof D hD a b ha hb dm dp hdm
  obtain ⟨CD1, C1, k1, ν1, _hCD1, hC1, hν1, hPh⟩ :=
    hPhys D hD a b ha hb dm dp hdm
  set C_D : ℝ := max CD0 CD1
  set C_tail : ℝ := C0 + C1
  set k_tail : ℕ := max k0 k1
  set ν₀ : ℝ := min (min ν0 ν1) 1
  refine ⟨C_D, C_tail, k_tail, ν₀, hCD0.trans (le_max_left CD0 CD1), add_pos hC0 hC1,
    lt_min (lt_min hν0 hν1) one_pos, ?_⟩
  intro p d hreg hν hPer Ke K0 hKe hK0 f σ S L
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν1_le : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν0_le : p.ν ≤ ν0 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1_le' : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hKe_bd := hPh C_D (le_max_right CD0 CD1) p d hreg hν1_le' hPer Ke hKe f
  have hK0_bd := hFlat C_D (le_max_left CD0 CD1) p d hreg hν0_le K0 hK0 f
  have hk0_le : (p.ν ^ k0)⁻¹ ≤ (p.ν ^ k_tail)⁻¹ :=
    velTail_inv_pow_mono hν_pos hν1_le (le_max_left k0 k1)
  have hk1_le : (p.ν ^ k1)⁻¹ ≤ (p.ν ^ k_tail)⁻¹ :=
    velTail_inv_pow_mono hν_pos hν1_le (le_max_right k0 k1)
  have hKe_bd' : hpIndNorm p.c (windowExtSet σ S L) (Ke f) ≤
      C1 * (p.ν ^ k_tail)⁻¹ * Real.exp (-D / p.ν) * ‖f‖ := by
    refine hKe_bd.trans ?_
    gcongr
  have hK0_bd' : hpIndNorm p.c (windowExtSet σ S L) (K0 f) ≤
      C0 * (p.ν ^ k_tail)⁻¹ * Real.exp (-D / p.ν) * ‖f‖ := by
    refine hK0_bd.trans ?_
    gcongr
  have hsub := hpIndNorm_sub_le (windowExtSet σ S L) (measurableSet_windowExtSet σ S L) (Ke f) (K0 f)
  calc hpIndNorm p.c (windowExtSet σ S L) (Ke f - K0 f)
      ≤ hpIndNorm p.c (windowExtSet σ S L) (Ke f) +
          hpIndNorm p.c (windowExtSet σ S L) (K0 f) := hsub
    _ ≤ C1 * (p.ν ^ k_tail)⁻¹ * Real.exp (-D / p.ν) * ‖f‖ +
          C0 * (p.ν ^ k_tail)⁻¹ * Real.exp (-D / p.ν) * ‖f‖ := add_le_add hKe_bd' hK0_bd'
    _ = C_tail * (p.ν ^ k_tail)⁻¹ * Real.exp (-D / p.ν) * ‖f‖ := by
        dsimp [C_tail]; ring

/-! ## 5. The physical exterior tail from the leaves `KOutChartAe` and `RawCoeffWindowTail` -/

/-- Restricted `eLpNorm` bound for any profile dominated on `S ∩ {s > 0}` by the graph
quantities `‖√s Qb‖, ‖√s Eb‖, ‖b‖` (measurability instead of `InHr`). -/
theorem eLpNorm_restrict_le_graph {c : ℝ} (hc : 0 < c) (G b Qb Eb : CProf)
    (hb : AEStronglyMeasurable b (hMeas c bgp))
    (hq : AEStronglyMeasurable (sqrtS Qb) (hMeas c bgp))
    (hη : AEStronglyMeasurable (sqrtS Eb) (hMeas c bgp)) (S : Set Coord) (hS : MeasurableSet S)
    {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hpt : ∀ x ∈ S, 0 < x.1 →
      ‖G x‖ ≤ A₁ * ‖sqrtS Qb x‖ + A₁ * ‖sqrtS Eb x‖ + A₂ * ‖b x‖) :
    eLpNorm G (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S) ≤
      ENNReal.ofReal A₁ * (hNorm c bgp (sqrtS Qb) + hNorm c bgp (sqrtS Eb)) +
        ENNReal.ofReal A₂ * hNorm c bgp b := by
  have hp1 : 1 ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]
    norm_num [bgp]
  have hae_pos : ∀ᵐ x ∂(hMeas c bgp), 0 < x.1 :=
    (Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)).mono fun x hx => hx.1
  let fq : Coord → ℝ := fun x => A₁ • ‖sqrtS Qb x‖
  let fη : Coord → ℝ := fun x => A₁ • ‖sqrtS Eb x‖
  let fb : Coord → ℝ := fun x => A₂ • ‖b x‖
  have hfq_m : AEStronglyMeasurable fq (hMeas c bgp) := hq.norm.const_smul A₁
  have hfη_m : AEStronglyMeasurable fη (hMeas c bgp) := hη.norm.const_smul A₁
  have hfb_m : AEStronglyMeasurable fb (hMeas c bgp) := hb.norm.const_smul A₂
  have hae_res : ∀ᵐ x ∂((hMeas c bgp).restrict S), ‖G x‖ ≤ ‖(fq + fη + fb) x‖ := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hae_pos] with x hxS hx0
    have hnn : 0 ≤ (fq + fη + fb) x := by
      change 0 ≤ A₁ * ‖sqrtS Qb x‖ + A₁ * ‖sqrtS Eb x‖ + A₂ * ‖b x‖
      positivity
    rw [Real.norm_of_nonneg hnn]
    exact hpt x hxS hx0
  have hmono1 : eLpNorm G (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S) ≤
      eLpNorm (fq + fη + fb) (ENNReal.ofReal bgp) (hMeas c bgp) :=
    (eLpNorm_mono_ae hae_res).trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hadd1 : eLpNorm (fq + fη + fb) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le (hfq_m.add hfη_m) hfb_m hp1
  have hadd2 : eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le hfq_m hfη_m hp1
  have hsmul_q : eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₁ * hNorm c bgp (sqrtS Qb) := by
    change eLpNorm (A₁ • fun x => ‖sqrtS Qb x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₁]
    rfl
  have hsmul_η : eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₁ * hNorm c bgp (sqrtS Eb) := by
    change eLpNorm (A₁ • fun x => ‖sqrtS Eb x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₁]
    rfl
  have hsmul_b : eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₂ * hNorm c bgp b := by
    change eLpNorm (A₂ • fun x => ‖b x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₂]
    rfl
  calc eLpNorm G (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S)
      ≤ eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) := hmono1.trans hadd1
    _ ≤ (eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp)) +
          eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) := add_le_add hadd2 le_rfl
    _ = ENNReal.ofReal A₁ * (hNorm c bgp (sqrtS Qb) + hNorm c bgp (sqrtS Eb)) +
          ENNReal.ofReal A₂ * hNorm c bgp b := by
        rw [hsmul_q, hsmul_η, hsmul_b, mul_add]

/-- A property holding a.e. on the open strip `s > 0, |q| < c/2` holds `hMeas c r`-a.e. (the
measure lives on `s > 0, -c/2 ≤ q < c/2`, and `q = -c/2` is Lebesgue-null). -/
theorem hMeas_ae_of_strip {c r : ℝ} (hc : 0 < c) {P : Coord → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)))),
      P x) :
    ∀ᵐ x ∂(hMeas c r), P x := by
  have hT : MeasurableSet (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) :=
    measurableSet_Ioi.prod (measurableSet_Ioo.prod MeasurableSet.univ)
  have h1 : ∀ᵐ x ∂(volume : Measure Coord),
      x ∈ Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) → P x :=
    (ae_restrict_iff' hT).1 h
  have hnull : (volume : Measure Coord) {x : Coord | x.2.1 = -c / 2} = 0 := by
    have hset : {x : Coord | x.2.1 = -c / 2} =
        (univ : Set ℝ) ×ˢ (({-c / 2} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
      ext x
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
      Measure.prod_prod]
    simp
  have h2 : ∀ᵐ x ∂(volume : Measure Coord), x.2.1 ≠ -c / 2 := by
    rw [ae_iff]
    simpa using hnull
  have hac : hMeas c r ≪ (volume : Measure Coord) := ageμ_ac_volume c (r / 2 - 5 / 2)
  have h3 : ∀ᵐ x ∂(hMeas c r), x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c :=
    Axi.ae_ageμ_mem hc (r / 2 - 5 / 2)
  filter_upwards [hac.ae_le h1, hac.ae_le h2, h3] with x h1x h2x h3x
  apply h1x
  obtain ⟨hs, hq⟩ := h3x
  exact ⟨hs, ⟨lt_of_le_of_ne hq.1.1 (Ne.symm h2x), hq.1.2⟩, trivial⟩

/-- Pointwise bound of the chart output by the weighted raw jet: if
`(1 + s)·chartJet b_raw ≤ e` at `x` (`s > 0`, `0 ≤ ε ≤ 1`), then
`‖kOutChart p b Qb Eb x‖ ≤ e‖√s Qb‖ + e‖√s Eb‖ + 3e‖b‖`. -/
theorem kOutChart_norm_le (p : Params) (b Qb Eb : CProf) {x : Coord} (hx : 0 < x.1)
    (hε0 : 0 ≤ p.ε) (hε1 : p.ε ≤ 1) {e : ℝ}
    (hJ : (1 + x.1) * chartJet (rawProf p) x ≤ e) :
    ‖kOutChart p b Qb Eb x‖ ≤ e * ‖sqrtS Qb x‖ + e * ‖sqrtS Eb x‖ + (3 * e) * ‖b x‖ := by
  set u : Coord → Axi.Merid := rawProf p with hu_def
  set J : ℝ := chartJet u x with hJ_def
  have hu0 : ‖u x‖ ≤ J := by
    simp only [hJ_def, chartJet]
    have := norm_nonneg (Axi.dQ u x)
    have := norm_nonneg (Axi.dEta u x)
    have := norm_nonneg (kAge u x)
    linarith
  have hqe : ‖qEps p.ε u x‖ + ‖Axi.dEta u x‖ ≤ J := by
    have h1 : ‖qEps p.ε u x‖ ≤ ‖Axi.dQ u x‖ + (‖kAge u x‖ + ‖u x‖) := by
      unfold qEps
      calc ‖Axi.dQ u x - p.ε • (kAge u x + u x)‖
          ≤ ‖Axi.dQ u x‖ + ‖p.ε • (kAge u x + u x)‖ := norm_sub_le _ _
        _ ≤ ‖Axi.dQ u x‖ + (‖kAge u x‖ + ‖u x‖) := by
          gcongr
          rw [norm_smul, Real.norm_of_nonneg hε0]
          calc p.ε * ‖kAge u x + u x‖ ≤ 1 * ‖kAge u x + u x‖ :=
                mul_le_mul_of_nonneg_right hε1 (norm_nonneg _)
            _ = ‖kAge u x + u x‖ := one_mul _
            _ ≤ ‖kAge u x‖ + ‖u x‖ := norm_add_le _ _
    simp only [hJ_def, chartJet]
    linarith
  have hJ0 : 0 ≤ J := le_trans (norm_nonneg _) hu0
  have hdiv : |chartDivR p.ε u x| ≤ 2 * J := by
    unfold chartDivR
    have h1 : |qEps p.ε u x 0| ≤ ‖qEps p.ε u x‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
    have h2 : |u x 0| ≤ ‖u x‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
    have h3 : |Axi.dEta u x 1| ≤ ‖Axi.dEta u x‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
    have h4 : |p.ε * u x 0| ≤ |u x 0| := by
      rw [abs_mul, abs_of_nonneg hε0]
      exact mul_le_of_le_one_left (abs_nonneg _) hε1
    calc |qEps p.ε u x 0 + p.ε * u x 0 + Axi.dEta u x 1|
        ≤ |qEps p.ε u x 0| + |p.ε * u x 0| + |Axi.dEta u x 1| := abs_add_three _ _ _
      _ ≤ 2 * J := by linarith
  have hsqrt_le : Real.sqrt x.1 ≤ 1 + x.1 := by
    have h := Real.sqrt_le_sqrt (show x.1 ≤ (1 + x.1) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have hsJ : x.1 * J ≤ e := le_trans (mul_le_mul_of_nonneg_right (by linarith) hJ0) hJ
  have hsu : Real.sqrt x.1 * ‖u x‖ ≤ e :=
    le_trans (mul_le_mul hsqrt_le hu0 (norm_nonneg _) (by linarith)) hJ
  have hsq : x.1 = Real.sqrt x.1 * Real.sqrt x.1 := (Real.mul_self_sqrt hx.le).symm
  have hnQ : ‖sqrtS Qb x‖ = Real.sqrt x.1 * ‖Qb x‖ := norm_sqrtS_of_nonneg Qb hx.le
  have hnE : ‖sqrtS Eb x‖ = Real.sqrt x.1 * ‖Eb x‖ := norm_sqrtS_of_nonneg Eb hx.le
  have hcp : ∀ F : Coord → Axi.Merid, ‖cplx F x‖ = ‖F x‖ := fun F => liftM_norm (F x)
  have hr0 : ‖(((u x 0 : ℝ) : ℂ))‖ ≤ ‖u x‖ := by
    rw [Complex.norm_real]; exact PiLp.norm_apply_le _ _
  have hr1 : ‖(((u x 1 : ℝ) : ℂ))‖ ≤ ‖u x‖ := by
    rw [Complex.norm_real]; exact PiLp.norm_apply_le _ _
  have hb0 : ‖b x 0‖ ≤ ‖b x‖ := PiLp.norm_apply_le _ _
  have hb1 : ‖b x 1‖ ≤ ‖b x‖ := PiLp.norm_apply_le _ _
  have hA : ‖((u x 0 : ℝ) : ℂ) • Qb x + ((u x 1 : ℝ) : ℂ) • Eb x‖ ≤
      ‖u x‖ * ‖Qb x‖ + ‖u x‖ * ‖Eb x‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    gcongr
  have hB : ‖b x 0 • cplx (qEps p.ε u) x + b x 1 • cplx (Axi.dEta u) x‖ ≤ ‖b x‖ * J := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, hcp, hcp]
    calc ‖b x 0‖ * ‖qEps p.ε u x‖ + ‖b x 1‖ * ‖Axi.dEta u x‖
        ≤ ‖b x‖ * ‖qEps p.ε u x‖ + ‖b x‖ * ‖Axi.dEta u x‖ := by gcongr
      _ = ‖b x‖ * (‖qEps p.ε u x‖ + ‖Axi.dEta u x‖) := by ring
      _ ≤ ‖b x‖ * J := mul_le_mul_of_nonneg_left hqe (norm_nonneg _)
  have hC : ‖((chartDivR p.ε u x : ℝ) : ℂ) • b x‖ ≤ 2 * J * ‖b x‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
  have hmain : ‖kOutChart p b Qb Eb x‖ ≤
      x.1 * ((‖u x‖ * ‖Qb x‖ + ‖u x‖ * ‖Eb x‖) + ‖b x‖ * J + 2 * J * ‖b x‖) := by
    unfold kOutChart
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hx.le]
    refine mul_le_mul_of_nonneg_left ?_ hx.le
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC
  refine hmain.trans ?_
  have hQe : x.1 * (‖u x‖ * ‖Qb x‖) ≤ e * ‖sqrtS Qb x‖ := by
    rw [hnQ]
    calc x.1 * (‖u x‖ * ‖Qb x‖) = (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Qb x‖) := by
          rw [show (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Qb x‖) =
            (Real.sqrt x.1 * Real.sqrt x.1) * (‖u x‖ * ‖Qb x‖) by ring, ← hsq]
      _ ≤ e * (Real.sqrt x.1 * ‖Qb x‖) :=
          mul_le_mul_of_nonneg_right hsu (by positivity)
  have hEe : x.1 * (‖u x‖ * ‖Eb x‖) ≤ e * ‖sqrtS Eb x‖ := by
    rw [hnE]
    calc x.1 * (‖u x‖ * ‖Eb x‖) = (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Eb x‖) := by
          rw [show (Real.sqrt x.1 * ‖u x‖) * (Real.sqrt x.1 * ‖Eb x‖) =
            (Real.sqrt x.1 * Real.sqrt x.1) * (‖u x‖ * ‖Eb x‖) by ring, ← hsq]
      _ ≤ e * (Real.sqrt x.1 * ‖Eb x‖) :=
          mul_le_mul_of_nonneg_right hsu (by positivity)
  have hbe : x.1 * (‖b x‖ * J + 2 * J * ‖b x‖) ≤ (3 * e) * ‖b x‖ := by
    calc x.1 * (‖b x‖ * J + 2 * J * ‖b x‖) = 3 * (x.1 * J) * ‖b x‖ := by ring
      _ ≤ 3 * e * ‖b x‖ := by gcongr
  calc x.1 * ((‖u x‖ * ‖Qb x‖ + ‖u x‖ * ‖Eb x‖) + ‖b x‖ * J + 2 * J * ‖b x‖)
      = x.1 * (‖u x‖ * ‖Qb x‖) + x.1 * (‖u x‖ * ‖Eb x‖) +
          x.1 * (‖b x‖ * J + 2 * J * ‖b x‖) := by ring
    _ ≤ e * ‖sqrtS Qb x‖ + e * ‖sqrtS Eb x‖ + (3 * e) * ‖b x‖ := by
        gcongr

/-- **`PhysKopWindowTransverseTailBound` from the two leaves** (SP 2007-2012, 2447-2455): the
identification `KOutChartAe` writes `K_εf` on the exterior slab as `kOutChart`, whose coefficients
are `≤ e^{-D/ν}` by `RawCoeffWindowTail`; the graph bound `profileGraphPhys_proof` (`T10`,
`r = 11/4`, `μ = 0`) controls `b, √s Q_εb, √s ∂_ηb` by `ν^{-1}‖f‖`. -/
theorem physKopWindowTransverseTailBound_of_leaves (hId : KOutChartAe)
    (hT : RawCoeffWindowTail) : PhysKopWindowTransverseTailBound := by
  intro D hD a b ha hb dm dp hdm
  obtain ⟨C_D₀, ν_T, hCD₀, hν_T, hTail⟩ := hT D hD a b ha hb dm dp hdm
  obtain ⟨C_G, hC_G, hG⟩ := profileGraphPhys_proof bgp (by norm_num [bgp])
    (by norm_num [bgp]) 0 (by norm_num [bgp])
  refine ⟨C_D₀, 4 * C_G, 1, min ν_T 1, hCD₀, by positivity, lt_min hν_T one_pos, ?_⟩
  intro C_D hCD p d hreg hν hper Ke hKe f σ S L
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hε_pos : 0 < p.ε := p.ε_pos
  have hν_T_le : p.ν ≤ ν_T := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.mpr
    have hd0 : 0 ≤ d := le_trans hreg.dm_pos.le hreg.dm_le
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd0) hν_pos.le
  have h2εc : 2 * p.ε * p.c ≤ 1 := hper
  obtain ⟨bε, hb_in, hb_resp, hKout⟩ := hKe f
  have hF_in : InHr p.c bgp (toProf p.c f) := inHr_toProf hc_pos f
  obtain ⟨_Sb, Qb, Eb, _hSb, hQb, hEb, hnorm⟩ :=
    (hG p.ν p.c p.ε hν_pos hc_pos hε_pos hε1 h2εc (toProf p.c f) hF_in).2 bε hb_resp
  have hg_in : InHr p.c bgp (toProf p.c (Ke f)) := inHr_toProf hc_pos (Ke f)
  have hae : toProf p.c (Ke f) =ᵐ[hMeas p.c bgp] kOutChart p bε Qb Eb :=
    hMeas_ae_of_strip hc_pos (hId p d dm dp hreg bε _ Qb Eb hb_in hg_in hQb hEb hKout)
  set E_exp : ℝ := Real.exp (-D / p.ν)
  have hE_nonneg : 0 ≤ E_exp := (Real.exp_pos _).le
  have hpt : ∀ x ∈ windowExtSet σ S L, 0 < x.1 →
      ‖kOutChart p bε Qb Eb x‖ ≤
        E_exp * ‖sqrtS Qb x‖ + E_exp * ‖sqrtS Eb x‖ + (3 * E_exp) * ‖bε x‖ := by
    intro x hx hx0
    exact kOutChart_norm_le p bε Qb Eb hx0 hε_pos.le hε1
      (hTail C_D hCD p d hreg hν_T_le x hx)
  have hsq_cont : Continuous fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)
  have hQm : AEStronglyMeasurable (sqrtS Qb) (hMeas p.c bgp) :=
    hsq_cont.aestronglyMeasurable.smul (HasWeakVec.aestronglyMeasurable_hMeas hQb)
  have hEm : AEStronglyMeasurable (sqrtS Eb) (hMeas p.c bgp) :=
    hsq_cont.aestronglyMeasurable.smul (HasWeakVec.aestronglyMeasurable_hMeas hEb)
  have hMeas_ext : MeasurableSet (windowExtSet σ S L) := measurableSet_windowExtSet σ S L
  have hRes := eLpNorm_restrict_le_graph hc_pos (kOutChart p bε Qb Eb) bε Qb Eb hb_in.meas
    hQm hEm (windowExtSet σ S L) hMeas_ext hE_nonneg (by positivity) hpt
  have hF_norm : hNorm p.c bgp (toProf p.c f) = ENNReal.ofReal ‖f‖ := by
    rw [hNorm_toProf hc_pos f, (ofReal_norm f).symm]
  have hν_le_sqrt : p.ν ≤ Real.sqrt p.ν := by
    calc p.ν = Real.sqrt p.ν * Real.sqrt p.ν := (Real.mul_self_sqrt hν_pos.le).symm
      _ ≤ 1 * Real.sqrt p.ν :=
          mul_le_mul_of_nonneg_right (by simpa using Real.sqrt_le_sqrt hν1) (Real.sqrt_nonneg _)
      _ = Real.sqrt p.ν := one_mul _
  have hν_inv_ge_one : 1 ≤ (p.ν ^ 1)⁻¹ := by
    rw [pow_one]
    exact one_le_inv₀ hν_pos |>.mpr hν1
  have hb_norm_le : hNorm p.c bgp bε ≤ ENNReal.ofReal (C_G * (p.ν ^ 1)⁻¹ * ‖f‖) := by
    have h1 : hNorm p.c bgp bε ≤ ENNReal.ofReal C_G * hNorm p.c bgp (toProf p.c f) :=
      (le_self_add.trans le_self_add).trans hnorm
    rw [hF_norm, ← ENNReal.ofReal_mul hC_G.le] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    calc C_G * ‖f‖ = C_G * 1 * ‖f‖ := by ring
      _ ≤ C_G * (p.ν ^ 1)⁻¹ * ‖f‖ := by gcongr
  have hgrad_norm_le :
      hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb) ≤
        ENNReal.ofReal (C_G * (p.ν ^ 1)⁻¹ * ‖f‖) := by
    have h1 : ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) ≤
        ENNReal.ofReal C_G * ENNReal.ofReal ‖f‖ := by
      rw [← hF_norm]
      calc ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))
          ≤ ENNReal.ofReal (Real.sqrt p.ν) *
              (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := by
            gcongr
        _ ≤ hNorm p.c bgp bε + hNorm p.c bgp _Sb +
              ENNReal.ofReal (Real.sqrt p.ν) *
                (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := le_add_self
        _ ≤ ENNReal.ofReal C_G * hNorm p.c bgp (toProf p.c f) := hnorm
    have h_inv_mul : ENNReal.ofReal p.ν⁻¹ * ENNReal.ofReal p.ν = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le), inv_mul_cancel₀ hν_pos.ne',
        ENNReal.ofReal_one]
    calc hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)
        = 1 * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := (one_mul _).symm
      _ = ENNReal.ofReal p.ν⁻¹ *
            (ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))) := by
          rw [← mul_assoc, h_inv_mul]
      _ ≤ ENNReal.ofReal p.ν⁻¹ * (ENNReal.ofReal C_G * ENNReal.ofReal ‖f‖) := by
          gcongr
      _ = ENNReal.ofReal (C_G * (p.ν ^ 1)⁻¹ * ‖f‖) := by
          rw [pow_one, ← ENNReal.ofReal_mul hC_G.le,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le)]
          congr 1; ring
  have hRes_toProf :
      eLpNorm (toProf p.c (Ke f)) (ENNReal.ofReal bgp)
          ((hMeas p.c bgp).restrict (windowExtSet σ S L)) ≤
        ENNReal.ofReal ((4 * C_G) * (p.ν ^ 1)⁻¹ * E_exp * ‖f‖) := by
    rw [eLpNorm_congr_ae (ae_restrict_of_ae hae)]
    calc eLpNorm (kOutChart p bε Qb Eb) (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (windowExtSet σ S L))
        ≤ ENNReal.ofReal E_exp * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) +
            ENNReal.ofReal (3 * E_exp) * hNorm p.c bgp bε := hRes
      _ ≤ ENNReal.ofReal E_exp * ENNReal.ofReal (C_G * (p.ν ^ 1)⁻¹ * ‖f‖) +
            ENNReal.ofReal (3 * E_exp) * ENNReal.ofReal (C_G * (p.ν ^ 1)⁻¹ * ‖f‖) := by
          gcongr
      _ = ENNReal.ofReal ((4 * C_G) * (p.ν ^ 1)⁻¹ * E_exp * ‖f‖) := by
          rw [← ENNReal.ofReal_mul hE_nonneg, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  exact hpIndNorm_le_of_restrict_toProf hc_pos (by positivity) (windowExtSet σ S L)
    hMeas_ext (Ke f) hRes_toProf

/-- **`WindowTransverseTailBound` from the two leaves** `KOutChartAe` and `RawCoeffWindowTail`
(the flat half is `flatK0opWindowTransverseTailBound_proof`). -/
theorem windowTransverseTailBound_of_leaves (hId : KOutChartAe) (hT : RawCoeffWindowTail) :
    UnforcedLeray.Short.IIb.WindowTransverseTailBound :=
  windowTransverseTailBound_of (physKopWindowTransverseTailBound_of_leaves hId hT)

/-- **`WindowTransverseTailBound` from the identification leaf alone**: the coefficient leaf is
`rawCoeffWindowTail_proof` (`TransverseTail/RawCoeff.lean`). -/
theorem windowTransverseTailBound_of_chartAe (hId : KOutChartAe) :
    UnforcedLeray.Short.IIb.WindowTransverseTailBound :=
  windowTransverseTailBound_of_leaves hId rawCoeffWindowTail_proof

/-- **`PartII-b:G3/2`**: proof of `WindowTransverseTailBound` (SP 463–467, 2447–2455). -/
theorem windowTransverseTailBound_proof : UnforcedLeray.Short.IIb.WindowTransverseTailBound :=
  windowTransverseTailBound_of_chartAe PhysKopYLKOut.kOutChartAe

end UnforcedLeray.Short.IIb

end
