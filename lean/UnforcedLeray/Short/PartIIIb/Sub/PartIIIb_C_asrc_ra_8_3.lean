import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8

/-!
# Decomposition of `rTrainBound` (`PartIII-b:C/asrc/ra/8/3`; source 5029-5032, 2040-2051, 4371)

Source: `the November 2 reference manuscript`.

`rTrain = (w·∇)h^p_A + (h^p_A·∇)w` with `w = v - Σ_jV_j`.  The pointwise bound
`‖rTrain‖ ≤ (‖h^p_A‖ + ‖Dh^p_A‖)(‖w‖ + ‖Dw‖)` reduces `RTrainBound` to a sup bound for `w` (the
fixed-band train-to-Gaussian comparison of Part I, `PartI.TrainComparison`), a cell `L²` bound of
`h^p_A, Dh^p_A` and measurability.  The combination is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- `‖h^p_A‖ + ‖D h^p_A‖` at `x`. -/
def hpAMag (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ‖hpA ν χ A s x‖ + ‖fderiv ℝ (hpA ν χ A s) x‖

/-- `‖w‖ + ‖Dw‖` at `x`, `w = v - Σ_jV_j`. -/
def trainDiffMag {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ‖trainPl tr s x - vsum ν s x‖ + ‖fderiv ℝ (fun y => trainPl tr s y - vsum ν s y) x‖

/-- **Sup bound of the train-to-Gaussian difference** (source 5029-5032, 2040-2051, 4371): on
`0 ≤ s ≤ 1.1/ν`, `‖v - Σ_jV_j‖_∞ + ‖D(v - Σ_jV_j)‖_∞ ≤ C ν^{-k} δ_base`.  From the fixed-band
comparison `PartI.TrainComparison` (`StatementsTrain.lean`, `sct:comparison`, with `j = 0, 1`,
`B0277.supNormD`) for the BUC train of `BgRegime.train_buc`, identifying the periodized Gaussian
`Vc` with the planar `Σ_jV_j` in the rescaled variables. -/
def RTrainSup : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ (Csig bsig C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < bsig ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν → ∀ x : ℝ × ℝ,
        trainDiffMag p.train s x ≤ C * p.ν⁻¹ ^ k * deltaBase Csig bsig p.ν

/-- **Cell `L²` bound of `h^p_A` and `Dh^p_A`** (source 4963-4977, 5029-5032, as for `RCrossBound`):
Gaussian sums, `‖h^p_A‖_{L²(cell)} + ‖Dh^p_A‖_{L²(cell)}`-type bound `C ν^{-k} M(A) s^{5/2}`, in the
normalized cell measure, together with a.e. measurability of the squared magnitude. -/
def HpAL2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
        AEMeasurable (fun x => ENNReal.ofReal (hpAMag p.ν χf A s x ^ 2))
            (UnforcedLeray.Cyl.avgμ p.c) ∧
        ∫⁻ x, ENNReal.ofReal (hpAMag p.ν χf A s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (5 / 2 : ℝ)) ^ 2)

/-- **Measurability of the train terms** (continuity of `rTrain` in `x` for `s > 0`: `h^p_A` is
`C²` in `x`, `v - Σ_jV_j` is `C¹`). -/
def RTrainMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (p : Params) (d dm dp : ℝ),
    UnforcedLeray.Short.IIb.BgRegime p d dm dp → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s →
        AEMeasurable (fun x => ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2))
          (UnforcedLeray.Cyl.avgμ p.c)

theorem norm_toMer_le (v : ℝ × ℝ) : ‖toMer v‖ ≤ 2 * ‖v‖ := by
  have h1 : |v.1| ≤ ‖v‖ := by simpa using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa using norm_snd_le v
  have : ‖toMer v‖ ≤ |v.1| + |v.2| := by
    unfold toMer
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two]
    simp
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs v.1, sq_abs v.2, mul_nonneg (abs_nonneg v.1) (abs_nonneg v.2)]
  linarith

theorem norm_rTrain_le {ν c : ℝ} (χf : ℝ → ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    ‖toMer (rTrain χf tr A s x)‖ ≤ 2 * (hpAMag ν χf A s x * trainDiffMag tr s x) := by
  refine (norm_toMer_le _).trans ?_
  unfold rTrain
  have a1 := (fderiv ℝ (hpA ν χf A s) x).le_opNorm (trainPl tr s x - vsum ν s x)
  have a2 := (fderiv ℝ (fun y => trainPl tr s y - vsum ν s y) x).le_opNorm (hpA ν χf A s x)
  have h1 := norm_nonneg (hpA ν χf A s x)
  have h2 := norm_nonneg (fderiv ℝ (hpA ν χf A s) x)
  have h3 := norm_nonneg (trainPl tr s x - vsum ν s x)
  have h4 := norm_nonneg (fderiv ℝ (fun y => trainPl tr s y - vsum ν s y) x)
  have := norm_add_le (fderiv ℝ (hpA ν χf A s) x (trainPl tr s x - vsum ν s x))
    (fderiv ℝ (fun y => trainPl tr s y - vsum ν s y) x (hpA ν χf A s x))
  unfold hpAMag trainDiffMag
  nlinarith [mul_nonneg h1 h3, mul_nonneg h1 h4, mul_nonneg h2 h3, mul_nonneg h2 h4]

theorem rTrainBound_of (as : ℝ) (χf : ℝ → ℝ) (h1 : RTrainSup) (h2 : HpAL2 as χf)
    (h3 : RTrainMeas as χf) : RTrainBound as χf := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨Cs, bs, C1, k1, n1, hb, hn1, H1⟩ := h1 dm dp hdm
  obtain ⟨C2, k2, n2, hn2, H2⟩ := h2 hχ dm dp hdm
  refine ⟨Cs, bs, 2 * (|C1| * |C2|), k1 + k2, min n1 n2, hb, lt_min hn1 hn2, ?_⟩
  intro p d hreg hν μ _ A hA s hs hs'
  have hν1 : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ n2 := hν.trans (min_le_right _ _)
  obtain ⟨m2, b2⟩ := H2 p d hreg hν2 A hA s hs hs'
  refine ⟨(h3 hχ p d dm dp hreg A hA s hs), ?_⟩
  set D := C1 * p.ν⁻¹ ^ k1 * deltaBase Cs bs p.ν with hD
  set E := C2 * p.ν⁻¹ ^ k2 * affM p.ν χf A * s ^ (5 / 2 : ℝ) with hE
  have hDb : ∀ x, trainDiffMag p.train s x ≤ |D| := fun x =>
    (H1 p d hreg hν1 s hs hs' x).trans (le_abs_self _)
  have hpt : ∀ x, ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2) ≤
      ENNReal.ofReal (4 * D ^ 2) * ENNReal.ofReal (hpAMag p.ν χf A s x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have a := norm_rTrain_le χf p.train A s x
    have hm : 0 ≤ hpAMag p.ν χf A s x := by unfold hpAMag; positivity
    have hd : 0 ≤ trainDiffMag p.train s x := by unfold trainDiffMag; positivity
    have hn : 0 ≤ ‖toMer (rTrain χf p.train A s x)‖ := norm_nonneg _
    have e1 : hpAMag p.ν χf A s x * trainDiffMag p.train s x ≤ hpAMag p.ν χf A s x * |D| :=
      mul_le_mul_of_nonneg_left (hDb x) hm
    have e2 : ‖toMer (rTrain χf p.train A s x)‖ ≤ 2 * (hpAMag p.ν χf A s x * |D|) := by linarith
    calc ‖toMer (rTrain χf p.train A s x)‖ ^ 2 ≤ (2 * (hpAMag p.ν χf A s x * |D|)) ^ 2 :=
          pow_le_pow_left₀ hn e2 2
      _ = 4 * D ^ 2 * hpAMag p.ν χf A s x ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]; ring
  calc ∫⁻ x, ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
      ≤ ∫⁻ x, ENNReal.ofReal (4 * D ^ 2) * ENNReal.ofReal (hpAMag p.ν χf A s x ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c) := lintegral_mono hpt
    _ = ENNReal.ofReal (4 * D ^ 2) * ∫⁻ x, ENNReal.ofReal (hpAMag p.ν χf A s x ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c) := lintegral_const_mul'' _ m2
    _ ≤ ENNReal.ofReal (4 * D ^ 2) * ENNReal.ofReal (E ^ 2) := by gcongr
    _ = ENNReal.ofReal ((2 * (|C1| * |C2|) * p.ν⁻¹ ^ (k1 + k2) * deltaBase Cs bs p.ν *
          affM p.ν χf A * s ^ (5 / 2 : ℝ)) ^ 2) := by
        have eD : D ^ 2 = (|C1| * (p.ν⁻¹ ^ k1 * deltaBase Cs bs p.ν)) ^ 2 := by
          rw [hD, show C1 * p.ν⁻¹ ^ k1 * deltaBase Cs bs p.ν =
            C1 * (p.ν⁻¹ ^ k1 * deltaBase Cs bs p.ν) by ring, mul_pow, mul_pow |C1|, sq_abs]
        have eE : E ^ 2 = (|C2| * (p.ν⁻¹ ^ k2 * affM p.ν χf A * s ^ (5 / 2 : ℝ))) ^ 2 := by
          rw [hE, show C2 * p.ν⁻¹ ^ k2 * affM p.ν χf A * s ^ (5 / 2 : ℝ) =
            C2 * (p.ν⁻¹ ^ k2 * affM p.ν χf A * s ^ (5 / 2 : ℝ)) by ring, mul_pow, mul_pow |C2|, sq_abs]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc (4 : ℝ), eD, eE, pow_add]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
