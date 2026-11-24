import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Assembly
import UnforcedLeray.Short.PartIIIb.Proofs.QSmallProof
import UnforcedLeray.Short.PartIIIb.Proofs.HSmallProof
import UnforcedLeray.Short.PartIIIb.Proofs.GainConvProof
import UnforcedLeray.Short.PartIIIb.Proofs.MixedReturnProof
import UnforcedLeray.Short.PartIIIb.Proofs.MRReduce
import UnforcedLeray.Short.PartIIIb.Proofs.MRCrossing
import UnforcedLeray.Short.PartIIIb.Proofs.SchurContinuity
import UnforcedLeray.Short.PartIIIb.Proofs.ScalarGain
import UnforcedLeray.Short.PartIIIb.Proofs.UnitRespExact
import UnforcedLeray.Short.PartIIIb.Proofs.MellinContinuous

/-!
# The closing argument on the concrete return sequence (source 5835-5985)

Source of record: `the November 2 reference manuscript` (73 pages).

`Concrete/ReturnInst.lean` defines the concrete sequence `S = concreteReturnSeq D G` (phase-locked
`ν_n = retNu`, the witness of `PhaseLocked.phaseLockedSequence`; `μ = μ_n(z) = muWin σ₀ ν_n z`).
This file states, for that `S`, the inputs of the closing argument as named targets and proves the
closing argument from them, reusing the proofs of `Proofs/QSmallProof.lean`,
`Proofs/HSmallProof.lean`, `Proofs/GainConvProof.lean` and `MixedReturnLemma`
(`Proofs/MixedReturnProof.lean`, with its three helpers).

## Targets for `S = concreteReturnSeq D G`

| target | source | supplied by |
|---|---|---|
| `ErrorFamilyBounds S γ ω_b m₀` | 5607-5627 | `errorFamilyBounds_of` (`Concrete/ReturnRepair/Estimates.lean`) from the numbered estimates `PartIII-b:C/rep/1-14`; assembled in task `PartIII-b:IIIb-D4` |
| `PairNormAndNearSolver S γ η_δ` | 5536-5547, 5640-5662 | `NearInst.pairNormAndNearSolver_concrete` (`NearInst/Link/Seq.lean`); also `concrete_pairNormAndNearSolver` (here) from `SeqData.NearSolverBounds` |
| `PLBound S a_s` | 5883-5891 | task `PartIII-b:C/rep/15` (`plBound_concrete`) |
| `CurvedFlatComparison S a_s c_N` | 5893-5901 | `NearInst.curvedFlatComparison_concrete` (`NearInst/Link/Seq.lean`) |
| `FlatLimit S λ κ ℓ₊ 𝒥 σ₀ a_s` | 4821-4845 | task `PartIII-b:IIIb-D3` (`flatLimit_concrete`) |
| `ConcreteReturnNormContinuity D G` | 5684-5685, 5918-5920 | organize item `ORG:return-concrete/repair-8/continuity` |
| `QSmall S γ` | 5666-5686, 5869-5872 | `concrete_qSmall` (here, `qSmall`) |
| `HSmall S` | 5893-5917 | `concrete_hSmall` (here, `hsmallProof`) |
| `GainConv S` | 5958-5968 | `concrete_gainConv` (here, `gainConvProof`) |
| `EnergyModes S` | 5969-5985 | `concrete_energyModes` (here, `spectral_assembly` with `MixedReturnLemma`) |

`γ = Re λ = gRate D.Pl`, `m₀ = D.K.m0`, `a_s = D.K.as`, `λ = D.Pl.eigenvalue`, `κ = D.Pl.kappa`,
`ℓ₊(H₀) = D.Pl.strainCoupling`, `𝒥 = planarJ D.Pl`.

## Large `n` only

The source works "for sufficiently small `ν`" (5679, 5945-5957) and on one fixed geometry per
level.  At a level where the near operator `D_N` is not a unit (`NearAt` fails) `concreteOps` is
an unspecified choice (`Classical.epsilon` of an empty predicate), so no statement about it is
intended there.  Accordingly:

* `ReturnSeq.shift S N` drops the first `N` levels; `spectral_assembly` and `T_qsmall` are applied
  to a shifted sequence and their conclusions transferred back (`qSmall_of_shift`,
  `energyModes_of_shift`);
* the operator-norm continuity of the source ("for each fixed geometry", 5684-5685, 5918-5920) is
  stated for large `n` (`ConcreteReturnNormContinuity`); the all-`n` form `ReturnNormContinuity S`
  constrains the unspecified operators of small levels and is not the source's statement.

The hypotheses `WardStressNormal`, `PhysAffineIdentity`, `HNilpotent` at large `n` (source
5796-5814) are the identities of the concrete base (`Concrete/PhysLayer.lean`:
`ReturnBase.wardStressNormal_of`, `physAffineIdentity_of`, `wardAffineNilpotent_of`, with the pins of
`Concrete/ReturnInst.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-! ## 1. Dropping finitely many levels -/

/-- The sequence `S` with its first `N` levels removed: level `n` of `S.shift N` is level `n + N`
of `S` (spaces, viscosity, operators and affine gradient). -/
def ReturnSeq.shift (S : ReturnSeq) (N : ℕ) : ReturnSeq where
  Vel n := S.Vel (n + N)
  Str n := S.Str (n + N)
  Src n := S.Src (n + N)
  Aff n := S.Aff (n + N)
  Gam n := S.Gam (n + N)
  Grd n := S.Grd (n + N)
  iVel n := S.iVel (n + N)
  sVel n := S.sVel (n + N)
  iStr n := S.iStr (n + N)
  sStr n := S.sStr (n + N)
  iSrc n := S.iSrc (n + N)
  sSrc n := S.sSrc (n + N)
  iAff n := S.iAff (n + N)
  sAff n := S.sAff (n + N)
  cAff n := S.cAff (n + N)
  iGam n := S.iGam (n + N)
  sGam n := S.sGam (n + N)
  cGam n := S.cGam (n + N)
  iGrd n := S.iGrd (n + N)
  sGrd n := S.sGrd (n + N)
  ν n := S.ν (n + N)
  ops n := S.ops (n + N)
  gradhA n := S.gradhA (n + N)

theorem ReturnSeq.shift_nu (S : ReturnSeq) (N n : ℕ) : (S.shift N).ν n = S.ν (n + N) := rfl

theorem errorFamilyBounds_shift {S : ReturnSeq} {γ ωb m0 : ℝ} (N : ℕ)
    (h : ErrorFamilyBounds S γ ωb m0) : ErrorFamilyBounds (S.shift N) γ ωb m0 := by
  obtain ⟨C, k, M, hM⟩ := h
  exact ⟨C, k, M, fun n hn z hz V => hM (n + N) (le_trans hn (Nat.le_add_right _ _)) z hz V⟩

theorem pairNormAndNearSolver_shift {S : ReturnSeq} {γ ηδ : ℝ} (N : ℕ)
    (h : PairNormAndNearSolver S γ ηδ) : PairNormAndNearSolver (S.shift N) γ ηδ := by
  obtain ⟨C, k, M, hM⟩ := h
  exact ⟨C, k, M, fun n hn z hz => hM (n + N) (le_trans hn (Nat.le_add_right _ _)) z hz⟩

theorem qSmall_of_shift {S : ReturnSeq} {γ : ℝ} (N : ℕ) (h : QSmall (S.shift N) γ) :
    QSmall S γ := by
  obtain ⟨C, k, M, hM⟩ := h
  refine ⟨C, k, M + N, fun n hn z hz => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
  exact hM m (by omega) z hz

theorem hSmall_shift {S : ReturnSeq} (N : ℕ) (h : HSmall S) : HSmall (S.shift N) := by
  unfold HSmall at h ⊢
  exact (tendsto_add_atTop_iff_nat N).2 h

theorem gainConv_shift {S : ReturnSeq} (N : ℕ) (h : GainConv S) : GainConv (S.shift N) := by
  unfold GainConv at h ⊢
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  exact (tendsto_add_atTop_nat N).eventually (h ε hε)

/-- The continuity clauses of `ReturnNormContinuity` at one level (source 5684-5685, 5918-5920). -/
def ReturnSeq.NormContinuousAt (S : ReturnSeq) (n : ℕ) : Prop :=
  ContinuousOn (fun z => (S.ops n z).P) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).Lg) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).Q) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).aMu) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).Lam) (Icc (-1) 1)

theorem returnNormContinuity_shift {S : ReturnSeq} {N : ℕ}
    (h : ∀ n ≥ N, S.NormContinuousAt n) : ReturnNormContinuity (S.shift N) :=
  fun n => h (n + N) (Nat.le_add_left _ _)

theorem energyModes_of_shift {S : ReturnSeq} (N : ℕ) (h : EnergyModes (S.shift N)) :
    EnergyModes S := by
  obtain ⟨z, hz0, hz⟩ := h
  refine ⟨fun n => if h : N ≤ n then z (n - N) else 0, ?_, ?_⟩
  · have h1 : Tendsto (fun n => z (n - N)) atTop (𝓝 0) :=
      hz0.comp (tendsto_sub_atTop_nat N)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [hn]
  · rw [eventually_atTop] at hz ⊢
    obtain ⟨K, hK⟩ := hz
    refine ⟨K + N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
    have hmK : K ≤ m := by omega
    have := hK m hmK
    have hN' : N ≤ m + N := Nat.le_add_left _ _
    have hzm : (if h : N ≤ m + N then z (m + N - N) else 0) = z m := by
      simp [hN']
    simp only [hzm]
    exact this

/-! ## 2. Two consequences of `QSmall` and `FlatLimit` used by the closing argument -/

/-- `sup_z ‖𝒬‖ < 1` for large `n` (source 5869-5872: `‖𝒬‖ ≤ P_ν e^{-γ/(100ν)} → 0`). -/
theorem supQ_lt_one_of_qSmall {S : ReturnSeq} {γ : ℝ} (hγ : 0 < γ) (hν0 : ∀ n, 0 < S.ν n)
    (hν : Tendsto S.ν atTop (𝓝 0)) (h : QSmall S γ) :
    ∀ᶠ n in atTop, (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖) < 1 := by
  obtain ⟨C, k, N, hN⟩ := h
  have hT := ((polyExp k (γ / 100) S.ν (div_pos hγ (by norm_num)) hν0 hν).1).const_mul C
  rw [mul_zero] at hT
  have hev := hT.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hev, eventually_ge_atTop N] with n h1 hn
  have : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  have hle : (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖) ≤
      C * ((S.ν n)⁻¹ ^ k * Real.exp (-(γ / 100) / S.ν n)) := by
    apply ciSup_le
    intro z
    have := hN n hn z z.2
    calc ‖(S.ops n z).Q‖ ≤ C * (S.ν n)⁻¹ ^ k * Real.exp (-(γ / 100) / S.ν n) := this
      _ = C * ((S.ν n)⁻¹ ^ k * Real.exp (-(γ / 100) / S.ν n)) := by ring
  linarith

/-- `sup ‖a_μ‖‖Λ_{μ,ν}‖ < ∞` on the window for large `n` (source 5905-5909), from the bounds
`‖a_μ‖ ≤ C`, `‖Λ‖ ≤ C A_*` of `FlatLimit` and `A_* = e^{-z}/(2|𝒞(σ₀)|)` (`astarExact`). -/
theorem aMuLam_bound_of_flatLimit {S : ReturnSeq} {lam κ ell : ℂ} {J : ℂ → ℂ} {σ₀ a_s : ℝ}
    (hC : mellinC lam ell J (σ₀ : ℂ) ≠ 0) (hν0 : ∀ n, 0 < S.ν n)
    (hν : Tendsto S.ν atTop (𝓝 0)) (h : FlatLimit S lam κ ell J σ₀ a_s) :
    ∃ (M : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
      ‖(S.ops n z).aMu‖ * ‖(S.ops n z).Lam‖ ≤ M := by
  obtain ⟨ωcan, C, k, γ', b, N, -, -, -, -, hN⟩ := h
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hν.eventually_lt_const one_pos)
  have hCpos : 0 < 2 * ‖mellinC lam ell J (σ₀ : ℂ)‖ := mul_pos two_pos (norm_pos_iff.2 hC)
  refine ⟨C * (C * (Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖))), max N N₁,
    fun n hn z hz => ?_⟩
  obtain ⟨-, ha, hl, -⟩ := hN n (le_of_max_le_left hn) z hz
  have hA := astarExact lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z hC (hν0 n)
    (hN₁ n (le_of_max_le_right hn))
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) ha
  have hAle : Astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z ≤
      Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖) := by
    rw [hA]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [hz.1])) hCpos.le
  have hl' : ‖(S.ops n z).Lam‖ ≤ C * (Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖)) :=
    hl.trans (mul_le_mul_of_nonneg_left hAle hC0)
  exact mul_le_mul ha hl' (norm_nonneg _) hC0

namespace Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 3. The planar coefficients of the concrete sequence -/

/-- `𝒞(σ) = (63πi/128) ℓ₊(H₀) Γ(σ+5/2) λ^{-σ-5/2} 𝒥(σ)` (source 5924-5926) is `mellinC` of the
planar data. -/
theorem signedCoeff_eq_mellinC (Pl : PlanarData) (σ : ℝ) :
    Pl.signedCoeff σ = mellinC Pl.eigenvalue Pl.strainCoupling (planarJ Pl) (σ : ℂ) := by
  simp only [UnforcedLeray.Blueprint.Planar.PlanarData.signedCoeff,
    UnforcedLeray.Blueprint.Planar.PlanarData.couplingL, mellinC, LCoeff, planarJ,
    Complex.ofReal_re]
  push_cast
  ring

theorem SeqData.mellinC_ne (D : SeqData) :
    mellinC D.Pl.eigenvalue D.Pl.strainCoupling (planarJ D.Pl) (D.σ₀ : ℂ) ≠ 0 := by
  rw [← signedCoeff_eq_mellinC]
  exact D.coeff_ne

/-- `ℓ₊(H₀) ≠ 0` (source 5931) follows from `𝒞(σ₀) ≠ 0`. -/
theorem SeqData.strainCoupling_ne (D : SeqData) : D.Pl.strainCoupling ≠ 0 := by
  intro h
  apply D.mellinC_ne
  simp [mellinC, LCoeff, h]

/-- The phase lock of the sequence (source 5935-5940) in the form of `T_gain`. -/
theorem SeqData.phase (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0) :
    ∀ᶠ n : ℕ in atTop, D.Pl.eigenvalue.im / retNu D.Pl D.σ₀ n -
        D.Pl.kappa.im * Real.log (retNu D.Pl D.σ₀ n) +
        Complex.arg (mellinC D.Pl.eigenvalue D.Pl.strainCoupling (planarJ D.Pl) (D.σ₀ : ℂ)) =
      2 * Real.pi * Real.sign D.Pl.eigenvalue.im * n := by
  rw [← signedCoeff_eq_mellinC]
  exact retNu_phase D.σ₀ hω

/-- Continuity of `𝒥` at `σ₀` on the real line gives continuity of `planarJ` at `σ₀`. -/
theorem planarJ_continuousAt {Pl : PlanarData} {σ : ℝ} (h : ContinuousAt Pl.mellinJ σ) :
    ContinuousAt (planarJ Pl) (σ : ℂ) := by
  have h' : ContinuousAt Pl.mellinJ (σ : ℂ).re := by simpa using h
  exact h'.comp Complex.continuous_re.continuousAt

/-! ## 4. The targets on the concrete sequence -/

variable (D : SeqData) (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)))

/-- The near layer of the sequence is invertible on the whole window for large `n` (source
3943-3951, 5862-5866). -/
def SeqData.NearEv : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z)

/-- **Operator-norm continuity on the concrete sequence** (source 5684-5685, 5918-5920: "for each
fixed geometry"), for large `n`: `z ↦ 𝒫, L, 𝒬, a_μ, Λ_{μ,ν}` at `μ = μ_n(z)` are norm continuous on
`[-1,1]`. -/
def ConcreteReturnNormContinuity : Prop :=
  ∀ᶠ n : ℕ in atTop, (concreteReturnSeq D G).NormContinuousAt n

/-- The near-solver bounds along the sequence (source 5536-5547, 5862-5866, the conclusions of
`NearInst.NearSolverC` at the levels): `‖G⁻¹D_N⁻¹G‖ ≤ Cν^{-k}` and `‖g⁻¹S_N g‖ ≤ Cν^{-k}e^{η_δ/ν}`
for the near operators `nearOpsAt` of the level at `μ = μ_n(z)`, for large `n`. -/
def SeqData.NearSolverBounds (C : ℝ) (k : ℕ) (ηδ : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ‖conjG (NearInst.gainEquiv (cOf (retNu D.Pl D.σ₀ n)) D.K.mZ ((D.level n).ρb D.Pl D.K)
        (gRate D.Pl) (D.level n).ν_pos)
        (Ring.inverse (nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).DN)‖ ≤
      C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k ∧
    ‖NearInst.gainConjS (gRate D.Pl) (D.level n).ν_pos
        (nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).SN‖ ≤
      C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k * Real.exp (ηδ / retNu D.Pl D.σ₀ n)

/-- **`PairNormAndNearSolver` on the concrete sequence** (source 5536-5547, 5640-5662): from the
near-solver bounds and the invertibility of the near layer for large `n`. -/
theorem concrete_pairNormAndNearSolver {C ηδ : ℝ} {k : ℕ} (hnear : D.NearEv)
    (hb : D.NearSolverBounds C k ηδ) :
    PairNormAndNearSolver (concreteReturnSeq D G) (gRate D.Pl) ηδ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Filter.Eventually.and hnear hb)
  refine ⟨(1 + Real.sqrt Real.pi) * |C|, k, N, fun n hn z hz => ?_⟩
  obtain ⟨hnr, hbn⟩ := hN n hn
  obtain ⟨hDN, hSN⟩ := hbn z hz
  have hnz := hnr z hz
  have hk0 : 0 ≤ (retNu D.Pl D.σ₀ n)⁻¹ ^ k := pow_nonneg (inv_nonneg.2 (retNu_pos _ _ _).le) k
  have hsq : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  refine ⟨fun T => ?_, fun T => ?_, fun V => concreteReturnSeq_pairNorm D G n z hnz V⟩
  · rw [concreteReturnSeq_ops_eq D G n z hnz]
    show ‖(nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).DNinvG (gRate D.Pl) (D.level n).ν_pos T‖ ≤ _
    refine (NearInst.NearOps.norm_DNinvG_le _ _ _ T).trans ?_
    refine mul_le_mul_of_nonneg_right (hDN.trans ?_) (norm_nonneg T)
    have h1 : C ≤ (1 + Real.sqrt Real.pi) * |C| := by
      nlinarith [le_abs_self C, abs_nonneg C, mul_nonneg hsq (abs_nonneg C)]
    exact mul_le_mul_of_nonneg_right h1 hk0
  · rw [concreteReturnSeq_ops_eq D G n z hnz]
    show ‖(nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).SNG (gRate D.Pl) (D.level n).ν_pos T‖ ≤ _
    have he : 0 ≤ Real.exp (ηδ / retNu D.Pl D.σ₀ n) := (Real.exp_pos _).le
    have hX : 0 ≤ (retNu D.Pl D.σ₀ n)⁻¹ ^ k * Real.exp (ηδ / retNu D.Pl D.σ₀ n) * ‖T‖ :=
      mul_nonneg (mul_nonneg hk0 he) (norm_nonneg T)
    have h1 : Real.sqrt Real.pi * C ≤ (1 + Real.sqrt Real.pi) * |C| := by
      have := mul_le_mul_of_nonneg_left (le_abs_self C) hsq
      nlinarith [abs_nonneg C]
    calc ‖(nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).SNG (gRate D.Pl) (D.level n).ν_pos T‖
        ≤ Real.sqrt Real.pi *
          ‖NearInst.gainConjS (gRate D.Pl) (D.level n).ν_pos
            (nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).SN‖ * ‖T‖ :=
          NearInst.NearOps.norm_SNG_le _ _ _ T
      _ ≤ Real.sqrt Real.pi * (C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k *
            Real.exp (ηδ / retNu D.Pl D.σ₀ n)) * ‖T‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSN hsq) (norm_nonneg T)
      _ = (Real.sqrt Real.pi * C) *
            ((retNu D.Pl D.σ₀ n)⁻¹ ^ k * Real.exp (ηδ / retNu D.Pl D.σ₀ n) * ‖T‖) := by ring
      _ ≤ ((1 + Real.sqrt Real.pi) * |C|) *
            ((retNu D.Pl D.σ₀ n)⁻¹ ^ k * Real.exp (ηδ / retNu D.Pl D.σ₀ n) * ‖T‖) :=
          mul_le_mul_of_nonneg_right h1 hX
      _ = (1 + Real.sqrt Real.pi) * |C| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k *
            Real.exp (ηδ / retNu D.Pl D.σ₀ n) * ‖T‖ := by ring

/-- **`QSmall` on the concrete sequence** (`repair:complete-graph-error`, `closure:Q-small`,
source 5666-5686, 5869-5872), by `qSmall` on a shifted sequence. -/
theorem concrete_qSmall {ωb ηδ : ℝ} (hγ : 0 < gRate D.Pl) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hωb0 : 0 ≤ ωb) (hm00 : 0 ≤ D.K.m0) (hηδ0 : 0 ≤ ηδ) (hωγ : ωb < gRate D.Pl / 1000)
    (hmγ : D.K.m0 < gRate D.Pl / 1000) (hηγ : ηδ < gRate D.Pl / 1000) (hnear : D.NearEv)
    (hEF : ErrorFamilyBounds (concreteReturnSeq D G) (gRate D.Pl) ωb D.K.m0)
    (hPN : PairNormAndNearSolver (concreteReturnSeq D G) (gRate D.Pl) ηδ) :
    QSmall (concreteReturnSeq D G) (gRate D.Pl) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnear
  refine qSmall_of_shift N ?_
  have hlim : Tendsto ((concreteReturnSeq D G).shift N).ν atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat N).2 (retNu_tendsto D.σ₀ hω)
  exact qSmall ((concreteReturnSeq D G).shift N) (gRate D.Pl) ωb D.K.m0 ηδ hγ hωb0 hm00 hηδ0
    hωγ hmγ hηγ (fun n => retNu_pos _ _ _) hlim
    (fun n z hz => concreteReturnSeq_isGraphLift D G (n + N) z
      (hN (n + N) (Nat.le_add_left _ _) z hz))
    (errorFamilyBounds_shift N hEF) (pairNormAndNearSolver_shift N hPN)

/-- **`HSmall` on the concrete sequence** (`r_n + h_n → 0`, source 5893-5917), by `hsmallProof`. -/
theorem concrete_hSmall {cN : ℝ} (hγ : 0 < gRate D.Pl) (hω : D.Pl.eigenvalue.im ≠ 0)
    (has : 0 < D.K.as) (hbud : 1.1 * D.K.as < min cN (gRate D.Pl / 100) / 4)
    (hQS : QSmall (concreteReturnSeq D G) (gRate D.Pl))
    (hPL : PLBound (concreteReturnSeq D G) D.K.as)
    (hCF : CurvedFlatComparison (concreteReturnSeq D G) D.K.as cN)
    (hFL : FlatLimit (concreteReturnSeq D G) D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling
      (planarJ D.Pl) D.σ₀ D.K.as) :
    HSmall (concreteReturnSeq D G) :=
  hsmallProof (concreteReturnSeq D G) D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling
    (planarJ D.Pl) D.σ₀ D.K.as cN hγ has D.mellinC_ne (fun n => retNu_pos _ _ _)
    (retNu_tendsto D.σ₀ hω) hbud hQS hPL hCF hFL

/-- **`GainConv` on the concrete sequence** (source 5958-5968), by `gainConvProof` with
`ScalarGainLimit` (`scalarGain`, `unitRespExact`, `mellinContinuousAt`). -/
theorem concrete_gainConv (hγ : 0 < gRate D.Pl) (hω : D.Pl.eigenvalue.im ≠ 0) (hσ : 0 < D.σ₀)
    (hJ : ContinuousAt D.Pl.mellinJ D.σ₀)
    (hFL : FlatLimit (concreteReturnSeq D G) D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling
      (planarJ D.Pl) D.σ₀ D.K.as) :
    GainConv (concreteReturnSeq D G) :=
  gainConvProof (scalarGain unitRespExact mellinContinuousAt) (concreteReturnSeq D G)
    D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl) D.σ₀ D.K.as hγ hω
    D.strainCoupling_ne (planarJ_continuousAt hJ) hσ D.mellinC_ne (fun n => retNu_pos _ _ _)
    (retNu_tendsto D.σ₀ hω) (D.phase hω) hFL

/-- **The closing argument on the concrete sequence** (`MixedReturnLemma` applied to
`S = concreteReturnSeq D G`, source 5835-5985): from the module inputs (error families, near
solver, `𝒫`/`L` bounds, curved-flat comparison, flat limit, norm continuity, and the exact
identities of the return system for large `n`) and the budget `η_δ, ω_b, m₀ < γ/1000`,
`1.1a_s < min{c_N, γ/100}/4`, there are `z_n → 0` and nonzero `T'`, `b` with `DT' = 0`,
`b = -S_{σ_n}T'`, `T' = Mb` at `σ_n = μ_n(z_n)` (source 5969-5985). -/
theorem concrete_energyModes {ωb ηδ cN : ℝ} (hγ : 0 < gRate D.Pl)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ : 0 < D.σ₀) (has : 0 < D.K.as)
    (hJ : ContinuousAt D.Pl.mellinJ D.σ₀)
    (hωb0 : 0 ≤ ωb) (hm00 : 0 ≤ D.K.m0) (hηδ0 : 0 ≤ ηδ) (hωγ : ωb < gRate D.Pl / 1000)
    (hmγ : D.K.m0 < gRate D.Pl / 1000) (hηγ : ηδ < gRate D.Pl / 1000)
    (hbud : 1.1 * D.K.as < min cN (gRate D.Pl / 100) / 4)
    (hnear : D.NearEv)
    (hW : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ((concreteReturnSeq D G).ops n z).WardStressNormal)
    (hA : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ((concreteReturnSeq D G).ops n z).PhysAffineIdentity)
    (hH : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ((concreteReturnSeq D G).ops n z).HNilpotent)
    (hcont : ConcreteReturnNormContinuity D G)
    (hEF : ErrorFamilyBounds (concreteReturnSeq D G) (gRate D.Pl) ωb D.K.m0)
    (hPN : PairNormAndNearSolver (concreteReturnSeq D G) (gRate D.Pl) ηδ)
    (hPL : PLBound (concreteReturnSeq D G) D.K.as)
    (hCF : CurvedFlatComparison (concreteReturnSeq D G) D.K.as cN)
    (hFL : FlatLimit (concreteReturnSeq D G) D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling
      (planarJ D.Pl) D.σ₀ D.K.as) :
    EnergyModes (concreteReturnSeq D G) := by
  have hν0 : ∀ n, 0 < (concreteReturnSeq D G).ν n := fun n => retNu_pos _ _ _
  have hνlim : Tendsto (concreteReturnSeq D G).ν atTop (𝓝 0) := retNu_tendsto D.σ₀ hω
  have hQS := concrete_qSmall D G hγ hω hωb0 hm00 hηδ0 hωγ hmγ hηγ hnear hEF hPN
  have hsmall := concrete_hSmall D G hγ hω has hbud hQS hPL hCF hFL
  have hgain := concrete_gainConv D G hγ hω hσ hJ hFL
  obtain ⟨M, N₁, hM⟩ := aMuLam_bound_of_flatLimit D.mellinC_ne hν0 hνlim hFL
  have hC := supQ_lt_one_of_qSmall hγ hν0 hνlim hQS
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (Filter.Eventually.and hnear (hW.and (hA.and (hH.and (Filter.Eventually.and hcont hC)))))
  set N := max N₁ N₂ with hNdef
  have hN : ∀ n ≥ N, (∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z)) ∧
      (∀ z ∈ Icc (-1 : ℝ) 1, ((concreteReturnSeq D G).ops n z).WardStressNormal) ∧
      (∀ z ∈ Icc (-1 : ℝ) 1, ((concreteReturnSeq D G).ops n z).PhysAffineIdentity) ∧
      (∀ z ∈ Icc (-1 : ℝ) 1, ((concreteReturnSeq D G).ops n z).HNilpotent) ∧
      (concreteReturnSeq D G).NormContinuousAt n ∧
      (⨆ z : Icc (-1 : ℝ) 1, ‖((concreteReturnSeq D G).ops n z).Q‖) < 1 :=
    fun n hn => hN₂ n (le_trans (le_max_right _ _) hn)
  refine energyModes_of_shift N ?_
  exact spectral_assembly (mixedReturn mrReduce mrCrossing schurContinuity)
    ((concreteReturnSeq D G).shift N)
    (fun n z hz => concreteReturnSeq_isNearInverse D G (n + N) z
      ((hN (n + N) (Nat.le_add_left _ _)).1 z hz))
    (fun n z hz => concreteReturnSeq_isGraphLift D G (n + N) z
      ((hN (n + N) (Nat.le_add_left _ _)).1 z hz))
    (fun n z hz => (hN (n + N) (Nat.le_add_left _ _)).2.1 z hz)
    (fun n z hz => (hN (n + N) (Nat.le_add_left _ _)).2.2.1 z hz)
    (fun n z hz => (hN (n + N) (Nat.le_add_left _ _)).2.2.2.1 z hz)
    (returnNormContinuity_shift fun n hn => (hN n hn).2.2.2.2.1) 0 M
    (fun n _ z hz => hM (n + N) (le_trans (le_max_left _ _) (Nat.le_add_left _ _)) z hz)
    (fun n _ => (hN (n + N) (Nat.le_add_left _ _)).2.2.2.2.2)
    (hSmall_shift N hsmall) (gainConv_shift N hgain)

end Concrete

end UnforcedLeray.Short.PartIIIb
