import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Decomposition of `rTrainSup` (`PartIII-b:C/asrc/ra/8/3/1`)

Source: `the November 2 reference manuscript`
5029-5032, 2040-2051, 2152-2161, 291-303 (`sct:comparison`), 4371.

`RTrainSup` follows from `PartI.TrainComparison` (proved by task `PartI:T09`), applied at `ρ = 2`
(`c = ν⁻² = trainPeriod 2 ν`, `BgRegime.c_eq`) to the BUC train `BgRegime.train_buc`, for `j = 0, 1`,
plus four bridge lemmas stated below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Train (width Vc)
open UnforcedLeray.Short.PartI (trainPeriod)

/-- **(1) Periodized Gaussian = `Σ_j V_j`** (source 4963-4977, 2040-2051): the planar sum
`vsum ν s = Σ_j V_j` equals the periodized heat vortex `Vc ν (ν²)⁻¹ s` (`Train.Vc`, period
`c = cOf ν`), componentwise, for `ν > 0`, `s ≥ 0`.  (`Vj` is the `j`-th translate of the isolated
vortex `a⁻² e^{-|x|²/(4a)} J x`, `a = 1 + νs`, which is `Train.isoV ν s`.) -/
def VsumEqVc : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 ≤ s → ∀ y : ℝ × ℝ,
    vsum ν s y = (Vc ν (cOf ν) s y 0, Vc ν (cOf ν) s y 1)

/-- **(2) Smoothness** of `v(s) - V_c(s)` for `s > 0` (source 2040-2051; the train is smooth for
`s > 0`, `B0140.TrainSol`, and `Vc` is a locally finite sum of Gaussians): `C¹` in `x`. -/
def TrainDiffSmooth : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < ν → ∀ s : ℝ, 0 < s →
    ContDiff ℝ 1 (fun z => tr.v s z - Vc ν c s z)

/-- **(3) From `supNormD` to the pointwise magnitude** (finite-dimensional, `j = 0, 1`): if
`g = v(s) - V_c(s)` is `C¹` with `‖g‖_∞ ≤ X0`, `‖Dg‖_∞ ≤ X1` (`B0277.supNormD`) and `Σ_jV_j` is the
planar copy of `V_c`, then `trainDiffMag tr s x ≤ X0 + X1` (the planar norm of
`(a 0, a 1)` is `≤ ‖a‖`; `fderiv = iteratedFDeriv 1` up to the linear isometry
`EuclideanSpace ℝ (Fin 2) → ℝ × ℝ`). -/
def DiffMagFromSup : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ),
    (∀ y : ℝ × ℝ, vsum ν s y = (Vc ν c s y 0, Vc ν c s y 1)) →
    ContDiff ℝ 1 (fun z => tr.v s z - Vc ν c s z) → ∀ X0 X1 : ℝ, 0 ≤ X0 → 0 ≤ X1 →
    UnforcedLeray.B0277.supNormD 0 (fun z => tr.v s z - Vc ν c s z) ≤ ENNReal.ofReal X0 →
    UnforcedLeray.B0277.supNormD 1 (fun z => tr.v s z - Vc ν c s z) ≤ ENNReal.ofReal X1 →
    ∀ x : ℝ × ℝ, trainDiffMag tr s x ≤ X0 + X1

/-- **(4) Exponential conversion** (source 291-303, 4371): the `sct:comparison` sup bounds
`C_j ν⁻¹ a^{-(5+j)/2} e^{-b_j c²/a}` (`a = width ν s = 1 + νs ∈ [1, 2.1]`, `c = ν^{-2}`) for `j = 0, 1`
are `≤ C ν^{-k} δ_base` for `0 < s ≤ 1.1/ν`, `ν` small, with `δ_base = exp(Csig/ν - bsig c²)`
(`c² = ν^{-4}`, `e^{-b c²/a} ≤ e^{-(b/2.1) c²}`; take `bsig = min(b_0,b_1)/3`, `Csig = 0` or any), and
`width ν s ≤ trainPeriod 2 ν ^ 2`. -/
def ComparisonExpConv : Prop :=
  ∀ C0 b0 C1 b1 : ℝ, 0 < C0 → 0 < b0 → 0 < C1 → 0 < b1 →
    ∃ (Csig bsig C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < bsig ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
        width ν s ≤ trainPeriod 2 ν ^ 2 ∧
        C0 * ν⁻¹ * width ν s ^ (-((5 + ((0 : ℕ) : ℝ)) / 2)) *
            Real.exp (-(b0 * trainPeriod 2 ν ^ 2 / width ν s)) ≤ C * ν⁻¹ ^ k * deltaBase Csig bsig ν ∧
        C1 * ν⁻¹ * width ν s ^ (-((5 + ((1 : ℕ) : ℝ)) / 2)) *
            Real.exp (-(b1 * trainPeriod 2 ν ^ 2 / width ν s)) ≤ C * ν⁻¹ ^ k * deltaBase Csig bsig ν

theorem trainPeriod_two_eq {ν : ℝ} (hν : 0 < ν) : trainPeriod 2 ν = cOf ν := by
  unfold UnforcedLeray.Short.PartI.trainPeriod cOf
  rw [show -(2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast]

theorem rTrainSup_of (hcmp : UnforcedLeray.Short.PartI.TrainComparison)
    (h1 : VsumEqVc) (h2 : TrainDiffSmooth) (h3 : DiffMagFromSup) (h4 : ComparisonExpConv) :
    RTrainSup := by
  intro dm dp hdm
  obtain ⟨C0, b0, n0, hC0, hb0, hn0, H0⟩ := hcmp 2 (by norm_num) 0
  obtain ⟨C1, b1, n1, hC1, hb1, hn1, H1⟩ := hcmp 2 (by norm_num) 1
  obtain ⟨Cs, bs, C, k, n2, hbs, hn2, H4⟩ := h4 C0 b0 C1 b1 hC0 hb0 hC1 hb1
  refine ⟨Cs, bs, 2 * C, k, min (min n0 n1) n2, hbs, lt_min (lt_min hn0 hn1) hn2, ?_⟩
  intro p d hreg hν s hs hs' x
  have hν0 : 0 < p.ν := p.ν_pos
  have hνn0 : p.ν ≤ n0 := (hν.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hνn1 : p.ν ≤ n1 := (hν.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hνn2 : p.ν ≤ n2 := hν.trans (min_le_right _ _)
  obtain ⟨hw, hb0', hb1'⟩ := H4 p.ν hν0 hνn2 s hs hs'
  have hcp : p.c = trainPeriod 2 p.ν := by
    rw [trainPeriod_two_eq hν0]; exact hreg.c_eq
  have main : ∀ c : ℝ, c = trainPeriod 2 p.ν → ∀ tr : UnforcedLeray.B0140.TrainSol p.ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      trainDiffMag tr s x ≤ 2 * C * p.ν⁻¹ ^ k * deltaBase Cs bs p.ν := by
    intro c hc tr hbuc
    subst hc
    obtain ⟨_, c0⟩ := H0 p.ν hν0 hνn0 tr hbuc s hs.le hw
    obtain ⟨_, c1⟩ := H1 p.ν hν0 hνn1 tr hbuc s hs.le hw
    have hV : ∀ y : ℝ × ℝ, vsum p.ν s y = (Vc p.ν (trainPeriod 2 p.ν) s y 0,
        Vc p.ν (trainPeriod 2 p.ν) s y 1) := by
      intro y
      rw [trainPeriod_two_eq hν0]; exact h1 p.ν s hν0 hs.le y
    have hw0 : 0 < width p.ν s := by
      have : 0 ≤ p.ν * s := by positivity
      simp only [width]; linarith
    have := h3 p.ν _ tr s hV (h2 p.ν _ tr hν0 s hs) _ _ (by positivity) (by positivity) c0 c1 x
    nlinarith [this, hb0', hb1']
  exact main p.c hcp p.train hreg.train_buc

end UnforcedLeray.Short.PartIIIb.Concrete
