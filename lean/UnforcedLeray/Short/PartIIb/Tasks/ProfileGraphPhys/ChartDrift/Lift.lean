import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_3
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.NicePhaseTest
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftPtw

/-!
# `PartII-b:T10/6/3/1` (`ChartLiftPairing`): the chart lift of a coordinate test

Source of record: `the November 2 reference manuscript`
lines 1912-1915 (`𝒯(√s b) = √s (S + 1/2) b`) and 1900-1906 (the lift `N_v`, the measure
`s^{-5/2} ds dq/c dη`, `P⁻¹ ∫∫ = π R² ∫`).

**Design.**  The phase test is the ring lift `N_v` of a *nice meridional profile*:
`liftTest c ε φ i = NvC ε⁻¹ (liftB c ε φ i)` where
`liftB c ε φ i (s, q, η) = (c ε² / π) s^{3/2} (∑_k φ(s, q + k c, η)) e_i`.
Then `liftB` is a `NiceProf`, so the proved `nvCNicePhaseTest_proof` (phase test) and
`nvCDriftPtw_proof` (`(∂_τ - ½ y·∇) N_v b = N_v (s ∂_s b + b/2)`) apply, and the pairing is
`dotL (N_v B) (N_v b) = s B·b`, which is `s^{5/2} (cε²/π) φ_per b_i` at the chart point; the phase
average `P⁻¹∫∫ = πR² ∫ ·  s^{-5/2} dq/c dη ds` (`Axi.phaseAvg_ringChart`, `R = ε⁻¹`) turns it into
`∫ b_i φ` after unfolding the `q`-periodization.

Each leaf below is a `Prop` with its own target theorem; this file proves the assembly
`chartLiftPairing_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace ChartLift

/-- The `c`-periodization in `q` of a coordinate function (a locally finite sum for a coordinate
test, since `tsupport φ` is compact). -/
def perCoord (c : ℝ) (φ : Coord → ℝ) (x : Coord) : ℝ :=
  ∑' k : ℤ, φ (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))

/-- The meridional profile `B = (c ε² / π) s^{3/2} φ_per e_i` whose ring lift is the test. -/
def liftB (c ε : ℝ) (φ : Coord → ℝ) (i : Fin 2) : CProf := fun x =>
  (((c * ε ^ 2 / Real.pi) * x.1 ^ ((3 : ℝ) / 2) * perCoord c φ x : ℝ) : ℂ) •
    (EuclideanSpace.single i (1 : ℂ) : CMerid)

/-- The lifted phase test `N_v B` (period `2εc`, `R = ε⁻¹`). -/
def liftTest (c ε : ℝ) (φ : Coord → ℝ) (i : Fin 2) : ℝ × Space → CVec3 :=
  NvC ε⁻¹ (liftB c ε φ i)

/-- The transposed-drift test `x ↦ Sᵗφ + φ/2` (`Sᵗφ = -∂_s(sφ)`, `S = s∂_s`). -/
def driftTest (φ : Coord → ℝ) : Coord → ℝ :=
  fun x => coordTranspose vS dZero φ x + (1 / 2 : ℝ) * φ x

/-- The integrand `x ↦ (cε²/π) s^{5/2} φ_per(x) b_i(x)` of the pairing at the chart point. -/
def pairG (c ε : ℝ) (φ : Coord → ℝ) (i : Fin 2) (b : CProf) : Coord → ℂ := fun x =>
  (((c * ε ^ 2 / Real.pi) * x.1 ^ ((5 : ℝ) / 2) * perCoord c φ x : ℝ) : ℂ) * b x i

/-! ## Leaves of (i): the lifted test is a phase test -/

/-- **Leaf `T10/6/3/1/1a`** (SP 1912, the `q`-periodization): smooth; the sum is locally finite
because `tsupport φ` is compact (`ContDiff` of a locally finite sum of smooth functions). -/
def PerSmooth : Prop :=
  ∀ (c : ℝ) (φ : Coord → ℝ), 0 < c → IsCoordTest φ → ContDiff ℝ ∞ (perCoord c φ)

/-- **Leaf `T10/6/3/1/1b`**: `c`-periodic in `q` (reindex the `ℤ`-sum by `k ↦ k + 1`). -/
def PerPeriodic : Prop :=
  ∀ (c : ℝ) (φ : Coord → ℝ) (x : Coord),
    perCoord c φ (qShift c x) = perCoord c φ x

/-- **Leaf `T10/6/3/1/1c`**: the periodization vanishes outside `s₀ ≤ s ≤ s₁`, `|η| ≤ L`
(`tsupport φ` is a compact subset of `s > 0`). -/
def PerVanish : Prop :=
  ∀ (c : ℝ) (φ : Coord → ℝ), 0 < c → IsCoordTest φ →
    ∃ s₀ s₁ L : ℝ, 0 < s₀ ∧ ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) →
      perCoord c φ x = 0

/-- **Leaf `T10/6/3/1/1`** (from 1a-1c): the lift profile is nice (smooth, periodic, supported in
a compact `s,η`-box with `s ≥ s₀ > 0`; `s^{3/2}` is smooth away from `s = 0`, where `B` vanishes
identically near `s ≤ s₀/2`). -/
def LiftNice : Prop :=
  ∀ (c ε : ℝ) (φ : Coord → ℝ) (i : Fin 2), 0 < c → 0 < ε → IsCoordTest φ →
    NiceProf c (liftB c ε φ i)

/-! ## Leaves of (iii): the drift of the lift is the lift of `Sᵗφ + φ/2` -/

/-- **Leaf `T10/6/3/1/3a`** (SP 1912-1915; `s·∂_s(s^{3/2} φ) = s^{3/2}(3/2 φ + s ∂_s φ)` and
`∂_s` commutes with the locally finite `q`-periodization): the profile of `Sᵗφ + φ/2` is
`(3/2) B - (s ∂_s B + B/2)`. -/
def LiftDriftProfile : Prop :=
  ∀ (c ε : ℝ) (φ : Coord → ℝ) (i : Fin 2), 0 < c → IsCoordTest φ →
    liftB c ε (driftTest φ) i = fun x =>
      (3 / 2 : ℂ) • liftB c ε φ i x -
        (x.1 • fderiv ℝ (liftB c ε φ i) x (cdir 0) + (1 / 2 : ℂ) • liftB c ε φ i x)

/-- **Leaf `T10/6/3/1/3b`** (`N_v` is `ℂ`-linear: `realC`, `Nv`, `frameL` are `ℝ`-linear in the
profile and `reM, imM` split a complex scalar): `N_v (a b - b') = a N_v b - N_v b'`. -/
def NvCLin : Prop :=
  ∀ (R : ℝ) (a : ℂ) (b b' : CProf) (p : ℝ × Space),
    NvC R (fun x => a • b x - b' x) p = a • NvC R b p - NvC R b' p

/-! ## Leaves of (ii): the pairing -/

/-- **Leaf `T10/6/3/1/2a`** (pointwise; `dotL (N_v B)(N_v b) = s B·b` since the frame is
orthonormal off the axis, and both sides vanish on the axis where `age = 0`):
`⟪liftTest, N_v b⟫(τ, y) = pairG (chart R (τ, y))`. -/
def PairPt : Prop :=
  ∀ (c ε : ℝ) (φ : Coord → ℝ) (i : Fin 2) (b : CProf) (p : ℝ × Space), 0 < ε →
    dotL (liftTest c ε φ i p) (NvC ε⁻¹ b p) =
      pairG c ε φ i b (Axi.chart ε⁻¹ p.1 p.2)

/-- **Leaf `T10/6/3/1/2b`** (SP 1900-1906: the complex-valued `Axi.phaseAvg_ringChart`; split into
positive/negative real and imaginary parts, or use `lintegral` of norms for integrability and the
real identity for each part): for measurable, `q`-periodic `G` integrable for `ageμ c (-5/2)`,
`P⁻¹ ∫_{(0,P]} ∫ G(chart) = π R² ∫ G d(ageμ c (-5/2))`, `P = 2c/R`. -/
def PhaseAvgC : Prop :=
  ∀ (R c : ℝ) (G : Coord → ℂ), 0 < R → 0 < c → Measurable G →
    (∀ s q η, G (s, (q + c, η)) = G (s, (q, η))) →
    Integrable G (Axi.ageμ c (-(5 / 2 : ℝ))) →
    phaseInt (2 * c / R) (fun p => G (Axi.chart R p.1 p.2)) =
      ((Real.pi * R ^ 2 : ℝ) : ℂ) * ∫ x, G x ∂(Axi.ageμ c (-(5 / 2 : ℝ)))

/-- **Leaf `T10/6/3/1/2c`** (unfolding the periodization against the cell; integrability of
`b_i φ` is `hrLocalIntegrable_proof`): for a measurable, everywhere `q`-periodic `b ∈ H_r`,
`pairG c ε φ i b` is `ageμ c (-5/2)`-integrable and
`∫ pairG d(ageμ c (-5/2)) = (ε²/π) ∫ b_i φ`. -/
def PairUnfold : Prop :=
  ∀ (c ε r : ℝ) (φ : Coord → ℝ) (i : Fin 2) (b : CProf), 0 < c → 0 < ε → 1 < r →
    IsCoordTest φ → InHr c r b → Measurable b →
    (∀ s q η, b (s, (q + c, η)) = b (s, (q, η))) →
    Integrable (pairG c ε φ i b) (Axi.ageμ c (-(5 / 2 : ℝ))) ∧
      ∫ x, pairG c ε φ i b x ∂(Axi.ageμ c (-(5 / 2 : ℝ))) =
        ((ε ^ 2 / Real.pi : ℝ) : ℂ) * ∫ x, b x i * (φ x : ℂ)

/-- **Leaf `T10/6/3/1/2d`** (a.e. classes: `periodicRepresentative` and `chartNullPullback`,
`Tasks/NvCNorm`): the pairing and the integral `∫ b_i φ` are unchanged under the measurable
periodic representative `b'` of `b ∈ H_r`:
`pairF P (liftTest) (N_v b) = pairF P (liftTest) (N_v b')` and `∫ b_i φ = ∫ b'_i φ`. -/
def PairRep : Prop :=
  ∀ (c ε r : ℝ) (φ : Coord → ℝ) (i : Fin 2) (b : CProf), 0 < c → 0 < ε → 1 < r →
    IsCoordTest φ → InHr c r b →
    ∃ b' : CProf, InHr c r b' ∧ Measurable b' ∧
      (∀ s q η, b' (s, (q + c, η)) = b' (s, (q, η))) ∧
      pairF (2 * ε * c) (liftTest c ε φ i) (NvC ε⁻¹ b) =
        pairF (2 * ε * c) (liftTest c ε φ i) (NvC ε⁻¹ b') ∧
      ∫ x, b x i * (φ x : ℂ) = ∫ x, b' x i * (φ x : ℂ)

/-- **Leaf `T10/6/3/1/2`** (from 2a-2d): `⟪liftTest, N_v b⟫ = ∫ b_i φ` for every `b ∈ H_r`. -/
def LiftPairing : Prop :=
  ∀ (c ε r : ℝ) (φ : Coord → ℝ) (i : Fin 2), 0 < c → 0 < ε → 1 < r → IsCoordTest φ →
    ∀ b : CProf, InHr c r b →
      pairF (2 * ε * c) (liftTest c ε φ i) (NvC ε⁻¹ b) = ∫ x, b x i * (φ x : ℂ)

/-! ## Assembly -/

theorem isCoordTest_driftTest {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (driftTest φ) := by
  have h1 := isCoordTest_coordTranspose_vS hφ
  refine ⟨h1.smooth.add (contDiff_const.mul hφ.smooth), ?_, ?_⟩
  · have h2 : HasCompactSupport (fun x : Coord => (1 / 2 : ℝ) * φ x) :=
      hφ.compact.mul_left
    exact h1.compact.add h2
  · refine (tsupport_add _ _).trans (Set.union_subset h1.supp ?_)
    exact (closure_mono (Function.support_mul_subset_right _ _)).trans hφ.supp

/-- The lifted test is a phase test. -/
theorem liftTest_isPhaseTest (hn : LiftNice) {c ε : ℝ} (φ : Coord → ℝ) (i : Fin 2)
    (hc : 0 < c) (hε : 0 < ε) (hφ : IsCoordTest φ) :
    IsPhaseTest (2 * ε * c) (liftTest c ε φ i) :=
  nvCNicePhaseTest_proof c ε _ hc hε (hn c ε φ i hc hε hφ)

/-- The transposed drift of the lifted test is the lift of `Sᵗφ + φ/2`. -/
theorem driftT_liftTest (hn : LiftNice) (hd : LiftDriftProfile) (hl : NvCLin) {c ε : ℝ}
    (φ : Coord → ℝ) (i : Fin 2) (hc : 0 < c) (hε : 0 < ε) (hφ : IsCoordTest φ) :
    driftT (liftTest c ε φ i) = liftTest c ε (driftTest φ) i := by
  funext p
  have hp := nvCDriftPtw_proof c ε _ hc hε (hn c ε φ i hc hε hφ) p
  unfold liftTest
  rw [hd c ε φ i hc hφ, hl]
  unfold driftT
  have hp' : NvC ε⁻¹ (fun x => x.1 • fderiv ℝ (liftB c ε φ i) x (cdir 0) +
      (1 / 2 : ℂ) • liftB c ε φ i x) p =
      dτ (NvC ε⁻¹ (liftB c ε φ i)) p - (1 / 2 : ℝ) • radialT (NvC ε⁻¹ (liftB c ε φ i)) p := hp.symm
  rw [hp']
  have h32 : (3 / 2 : ℂ) • NvC ε⁻¹ (liftB c ε φ i) p = (3 / 2 : ℝ) • NvC ε⁻¹ (liftB c ε φ i) p := by
    rw [← Complex.coe_smul]
    norm_num
  rw [h32]
  abel

/-- **Assembly of `T10/6/3/1`**: `ChartLiftPairing` from the leaves. -/
theorem chartLiftPairing_of (hn : LiftNice) (hd : LiftDriftProfile) (hl : NvCLin)
    (hp : LiftPairing) : ChartLiftPairing := by
  intro c ε r φ i hc hε hr hφ
  refine ⟨liftTest c ε φ i, liftTest_isPhaseTest hn φ i hc hε hφ, fun b hb => ⟨hp c ε r φ i hc hε hr hφ b hb, ?_⟩⟩
  rw [driftT_liftTest hn hd hl φ i hc hε hφ,
    hp c ε r (driftTest φ) i hc hε hr (isCoordTest_driftTest hφ) b hb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [driftTest]

end ChartLift

end UnforcedLeray.Short.IIb
