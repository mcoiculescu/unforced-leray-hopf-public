import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.Series
import UnforcedLeray.Infra.VolterraEvolution.Kernel
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.LapPMul

/-!


Source of record: `the November 2 reference manuscript`, lines 2100-2105 (the regular
problem behind the duality argument; the source treats it as standard parabolic theory) and 2085-2093
(`TrainClose` bounds only `D^j v`, `j ≤ 4`, whence the LOCAL regularity).

`locStep_of` here proves `LocStep` from the leaves below, and each leaf is proved in this folder:
`TruncDrift`, `FreeCB`, `GLinear`, `GainZero`, `GainOne`, `CommGain` in `Gains.lean`,
`ClassicalToMild` in `Mild.lean`; the assembly is `LS.locStep_proved` in `Final.lean`.

## The mathematics

Write `G F (σ) = ∫₀^σ e^{ν(σ-r)Δ} F(r) dr` (`duhamelConv ν 0 F`).  Let `u ∈ C^k` on `|η| < ρ + 3`
(`k ≥ 2`), `ψ = 1` on `|η| ≤ ρ + 1`, `ψ = 0` on `|η| > ρ + 2`, `θ = 1` on `|η| ≤ ρ + 5/2`, `θ = 0` on
`|η| > ρ + 3`, `φ = 1` on `|η| ≤ ρ`, `φ = 0` on `|η| > ρ + 1/2`.

1. `b = θ w` has every derivative bounded (`TruncDrift`), `Y = ψ u` is `C^k_b` and solves classically
   `Y_σ = νΔY - b·∇Y + g`, `g = -2νψ'∂_η u - νψ''u + b_η ψ'u ∈ C^{k-1}_b`, `g = 0` off
   `ρ + 1 ≤ |η| ≤ ρ + 2` (`localPde`).  Hence `Y = e^{νσΔ}(ψ f) + G[-b·∇Y + g]` (`ClassicalToMild`).
2. Differentiating `k - 1` times reduces the gain of one derivative to order one (`gainStep`, an
   induction on the order which differentiates the mild equation with `∂_j G F = G ∂_j F`,
   `GainOne`): lower order terms of the drift go into a `C^m_b` forcing `h`, the derivatives of `g`
   into a forcing `p` that vanishes on `supp φ`.
3. Order one (`levelOne_of`): if `y ∈ C¹_b`, `y = S - G[b·∇y]`, `S ∈ C¹_b`, `φS ∈ C²_b`, then
   `φy ∈ C²_b`.  This is the Picard iteration in the class `{Z ∈ C¹_b : φZ ∈ C²_b}`, abstractly
   `neumannX` (`Series.lean`).  The map `Z ↦ G[b·∇Z]` halves the exponentially weighted norms of the
   class: `C¹_b → C¹_b` by the gain `G : C⁰_b → C¹_b` (`GainZero`), and
   `φ G[b·∇Z] = G[b·∇(φZ) - (b·∇φ) Z] + [φ, G][b·∇Z]`, where `G : C¹_b → C²_b` (`GainOne`) and the
   commutator `[φ, G] : C⁰_b → C²_b` gains two derivatives (`CommGain`: its kernel
   `(φ(x) - φ(y)) K_a(x - y)` carries the factor `|x - y|`, which is `a^{1/2}` in parabolic scaling).
   The forcing `p` needs no separate off-diagonal estimate: `φ p = 0` gives `φ G p = [φ, G] p`.
   Uniqueness in `C¹_b` is the same contraction.

Two simplifications of the plan of the organizer task: the induction of step 2 replaces `ConvRegular`
and the commutator gain at a general order `k` by their order-one forms, and the commutator replaces
the separate off-diagonal smoothness of `G`.

## Leaves

* `TruncDrift` (`/1`): `θ w` is `C^m_b` for every `m`;
* `FreeCB` (`/2`): `σ ↦ e^{νσΔ} f` is `C^m_b` for every `m` and every test function `f`;
* `GLinear` (`/3`): `G` is linear;
* `GainZero` (`/4`), `GainOne` (`/5`): `G : C⁰_b → C¹_b`, `G : C¹_b → C²_b`, with Volterra bounds;
* `CommGain` (`/6`): `[φ, G] : C⁰_b → C²_b`, with a Volterra bound;
* `ClassicalToMild` (`/7`): a classical `C²_b` solution of `Y_σ = νΔY + F` satisfies Duhamel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

variable {T : ℝ}

/-! ## Definitions of the leaves -/

/-- The Volterra bound `K ∫₀^σ (1 + (σ - r)^{-1/2}) b(r) dr`. -/
def Kconv (K : ℝ) (b : ℝ → ℝ) (σ : ℝ) : ℝ :=
  K * ∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * b r

/-- The commutator `[ψ, G] F = ψ G F - G (ψ F)`. -/
def comm (ν : ℝ) (ψ : ℝ → ℝ) (F : ℝ → Pl → ℝ) : ℝ → Pl → ℝ :=
  fun σ x => ψ x.2 * duhamelConv ν 0 F σ x - duhamelConv ν 0 (mulC ψ F) σ x

/-- **Leaf `/1`** (SP 2085-2093, 2100-2105): a jointly smooth `c`-periodic function, cut off in `η`,
is `C^m_b` on `[0, T] × ℝ²` for every `m`: the derivatives are jointly continuous, periodic, and so
bounded on the compact `η`-range of the cutoff (`pdJointSmooth`, `pdPeriodic`, `bandBounded`). -/
def TruncDrift : Prop :=
  ∀ (c T R : ℝ) (U : ℝ → Pl → ℝ) (θ : ℝ → ℝ), 0 < c →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => U z.1 z.2) (Icc 0 T ×ˢ univ) →
    (∀ σ ∈ Icc 0 T, ∀ x : Pl, U σ (x.1 + c, x.2) = U σ x) → IsCut R θ →
    ∀ m : ℕ, CB T m (mulC θ U)

/-- **Leaf `/2`** (SP 2100-2105, "Duhamel for a smooth compactly supported datum"): the free evolution
of a cylinder test function is `C^m_b` on `[0, T] × ℝ²` for every `m` (`heatCommute`,
`heatGradFormula`, `heatCont`, `heatWBounds`; induct on `m` with `IsCylTest.pd`). -/
def FreeCB : Prop :=
  ∀ (c ν T : ℝ) (f : Pl → ℝ), 0 < c → 0 < ν → 0 ≤ T → B0579.IsCylTest c f →
    ∀ m : ℕ, CB T m (fun σ => heatSG (ν * σ) f)

/-- **Leaf `/3`** (SP 2100-2105): linearity of the Duhamel convolution on compactly `η`-supported
bounded continuous integrands. -/
def GLinear : Prop :=
  ∀ (ν T R : ℝ) (F F' : ℝ → Pl → ℝ) (c : ℝ), 0 < ν → 0 ≤ T → CB T 0 F → CB T 0 F' → EtaS T R F →
    EtaS T R F' → ∀ σ ∈ Icc 0 T, ∀ x : Pl,
      duhamelConv ν 0 (fun r y => F r y + F' r y) σ x =
        duhamelConv ν 0 F σ x + duhamelConv ν 0 F' σ x ∧
      duhamelConv ν 0 (fun r y => c * F r y) σ x = c * duhamelConv ν 0 F σ x

/-- **Leaf `/4`** (SP 2100-2105): `G : C⁰_b → C¹_b` with a Volterra bound, on compactly `η`-supported
integrands (`dDiff`, `dCont`, the generic continuity `CC.gen_cont` of `crCont`, `heatWBounds`). -/
def GainZero : Prop :=
  ∀ (ν T R : ℝ), 0 < ν → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (F : ℝ → Pl → ℝ) (b : ℝ → ℝ), CB T 0 F → EtaS T R F → ContinuousOn b (Icc 0 T) →
      (∀ r ∈ Icc 0 T, 0 ≤ b r) → CBle T 0 F b →
      CB T 1 (duhamelConv ν 0 F) ∧ CBle T 1 (duhamelConv ν 0 F) (Kconv K b)

/-- **Leaf `/5`** (SP 2100-2105): `G : C¹_b → C²_b` with a Volterra bound and `∂_j G F = G ∂_j F`, on
compactly `η`-supported integrands (`convRegular`, `crDeriv_of`, `heatSGd_eq_heatSG_pd`). -/
def GainOne : Prop :=
  ∀ (ν T R : ℝ), 0 < ν → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (F : ℝ → Pl → ℝ) (b : ℝ → ℝ), CB T 1 F → EtaS T R F → ContinuousOn b (Icc 0 T) →
      (∀ r ∈ Icc 0 T, 0 ≤ b r) → CBle T 1 F b →
      CB T 2 (duhamelConv ν 0 F) ∧ CBle T 2 (duhamelConv ν 0 F) (Kconv K b) ∧
      ∀ σ ∈ Icc 0 T, ∀ (j : Fin 2) (x : Pl),
        B0579.pd j (duhamelConv ν 0 F σ) x = duhamelConv ν 0 (fun r => B0579.pd j (F r)) σ x

/-- **Leaf `/6`** (SP 2100-2105): the commutator gains two derivatives: `[ψ, G] : C⁰_b → C²_b` with a
Volterra bound.  Its kernel is `(ψ(x₂) - ψ(y₂)) K_a(x - y)`, and `|x₂ - y₂|` is `a^{1/2}` in
parabolic scaling, so that the second derivatives have the integrable size `a^{-1/2}`. -/
def CommGain : Prop :=
  ∀ (ν T R R' : ℝ) (ψ : ℝ → ℝ), 0 < ν → 0 ≤ T → IsCut R' ψ → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (F : ℝ → Pl → ℝ) (b : ℝ → ℝ), CB T 0 F → EtaS T R F → ContinuousOn b (Icc 0 T) →
      (∀ r ∈ Icc 0 T, 0 ≤ b r) → CBle T 0 F b →
      CB T 2 (comm ν ψ F) ∧ CBle T 2 (comm ν ψ F) (Kconv K b)

/-- **Leaf `/7`** (SP 2100-2105): a classical `C²_b` solution of `Y_σ = νΔY + F` with `Y`, `F`
compactly supported in `η` satisfies Duhamel's formula: differentiate
`r ↦ e^{ν(s-r)Δ} Y(r)` (`heatLapTransfer`, `HTD.heatK_hasDerivAt_b`). -/
def ClassicalToMild : Prop :=
  ∀ (ν T R : ℝ) (Y F : ℝ → Pl → ℝ), 0 < ν → 0 ≤ T → CB T 2 Y → EtaS T R Y → CB T 0 F → EtaS T R F →
    (∀ σ ∈ Icc 0 T, ∀ x : Pl,
      HasDerivWithinAt (fun r => Y r x) (ν * lapP (Y σ) x + F σ x) (Icc 0 T) σ) →
    ∀ s ∈ Icc 0 T, ∀ x : Pl, Y s x = heatSG (ν * s) (Y 0) x + duhamelConv ν 0 F s x

/-! ## Elementary facts on the convolution and the drift term -/

theorem CBle.neg : ∀ {m : ℕ} {Z : ℝ → Pl → ℝ} {b : ℝ → ℝ}, CBle T m Z b →
    CBle T m (fun σ x => -Z σ x) b
  | 0, _, _, h => fun σ hσ x => by rw [abs_neg]; exact h σ hσ x
  | m + 1, Z, b, h => by
      refine ⟨fun σ hσ x => by rw [abs_neg]; exact h.1 σ hσ x, fun j => ?_⟩
      refine CBle.congr (CBle.neg (h.2 j)) fun σ _ x => ?_
      show -B0579.pd j (Z σ) x = B0579.pd j (fun y => -Z σ y) x
      unfold B0579.pd
      rw [fderiv_fun_neg]
      rfl

/-- The convolution only sees `F` on `[0, T]`. -/
theorem G_congr {ν : ℝ} {F F' : ℝ → Pl → ℝ} (e : ∀ r ∈ Icc 0 T, ∀ x : Pl, F r x = F' r x) :
    ∀ σ ∈ Icc 0 T, ∀ x : Pl, duhamelConv ν 0 F σ x = duhamelConv ν 0 F' σ x := by
  intro σ hσ x
  unfold duhamelConv
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hσ.1] at hr
  have : F r = F' r := funext (e r ⟨hr.1, hr.2.trans hσ.2⟩)
  simp only [this]

/-- `G 0 = 0`. -/
theorem G_zero {ν : ℝ} (σ : ℝ) (x : Pl) : duhamelConv ν 0 (fun _ _ => 0) σ x = 0 := by
  unfold duhamelConv
  have : ∀ a : ℝ, heatSG a (fun _ => 0) x = 0 := fun a => by
    unfold heatSG
    split_ifs <;> simp
  simp [this]

theorem trm_cb {m : ℕ} {b0 b1 Z : ℝ → Pl → ℝ} (h0 : CB T m b0) (h1 : CB T m b1)
    (hZ : CB T (m + 1) Z) : CB T m (trm b0 b1 Z) :=
  CB.add (CB.mul h0 (hZ.2.2 0)) (CB.mul h1 (hZ.2.2 1))

theorem trm_etaS {R : ℝ} {b0 b1 : ℝ → Pl → ℝ} (Z : ℝ → Pl → ℝ) (h0 : EtaS T R b0)
    (h1 : EtaS T R b1) : EtaS T R (trm b0 b1 Z) :=
  EtaS.add (EtaS.mul_right _ h0) (EtaS.mul_right _ h1)

theorem trm_add {m : ℕ} {b0 b1 Z Z' : ℝ → Pl → ℝ} (hZ : CB T (m + 1) Z) (hZ' : CB T (m + 1) Z')
    (σ : ℝ) (hσ : σ ∈ Icc 0 T) (x : Pl) :
    trm b0 b1 (fun r y => Z r y + Z' r y) σ x = trm b0 b1 Z σ x + trm b0 b1 Z' σ x := by
  unfold trm
  rw [pd_add 0 (hZ.2.1 σ hσ x) (hZ'.2.1 σ hσ x), pd_add 1 (hZ.2.1 σ hσ x) (hZ'.2.1 σ hσ x)]
  ring

theorem trm_smul {m : ℕ} {b0 b1 Z : ℝ → Pl → ℝ} (c : ℝ) (hZ : CB T (m + 1) Z)
    (σ : ℝ) (hσ : σ ∈ Icc 0 T) (x : Pl) :
    trm b0 b1 (fun r y => c * Z r y) σ x = c * trm b0 b1 Z σ x := by
  unfold trm
  have hc : DifferentiableAt ℝ (fun _ : Pl => c) x := differentiableAt_const c
  rw [pd_mul 0 hc (hZ.2.1 σ hσ x), pd_mul 1 hc (hZ.2.1 σ hσ x), pd_const, pd_const]
  ring

theorem dCut_zero (ψ : ℝ → ℝ) (t : ℝ) : dCut ψ 0 t = 0 := by simp [dCut]

theorem dCut_one (ψ : ℝ → ℝ) (t : ℝ) : dCut ψ 1 t = deriv ψ t := by simp [dCut]

/-- The partials of `ψ Z`. -/
theorem pd_mulC {ψ : ℝ → ℝ} {f : Pl → ℝ} {x : Pl} (hψ : Differentiable ℝ ψ)
    (hf : DifferentiableAt ℝ f x) (j : Fin 2) :
    B0579.pd j (fun y => ψ y.2 * f y) x = ψ x.2 * B0579.pd j f x + f x * dCut ψ j x.2 := by
  have h := pd_mul j (f := fun y : Pl => ψ y.2) (g := f) (x := x)
    ((hψ.comp differentiable_snd) x) hf
  rw [pd_cut hψ] at h
  exact h

/-- `ψ (b·∇Z) = b·∇(ψ Z) - (b₁ ψ') Z`. -/
theorem mulC_trm {ψ : ℝ → ℝ} {b0 b1 Z : ℝ → Pl → ℝ} {m : ℕ} (hψ : Differentiable ℝ ψ)
    (hZ : CB T (m + 1) Z) (σ : ℝ) (hσ : σ ∈ Icc 0 T) (x : Pl) :
    mulC ψ (trm b0 b1 Z) σ x = trm b0 b1 (mulC ψ Z) σ x -
      (b1 σ x * cutF (deriv ψ) σ x) * Z σ x := by
  have h0 := pd_mulC hψ (hZ.2.1 σ hσ x) 0
  have h1 := pd_mulC hψ (hZ.2.1 σ hσ x) 1
  rw [dCut_zero] at h0
  rw [dCut_one] at h1
  unfold mulC trm cutF
  rw [h0, h1]
  ring

/-! ## The weights -/

theorem ew_continuous (lam M : ℝ) : Continuous (ew lam M) := by
  unfold ew
  fun_prop

/-- `Kconv` of an exponential weight. -/
theorem Kconv_ew (K lam M σ : ℝ) :
    Kconv K (ew lam M) σ =
      K * M * ∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r) := by
  unfold Kconv ew
  have : ∀ r : ℝ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (M * Real.exp (lam * r)) =
      M * ((1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r)) := fun r => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The integral of the weight is nonnegative. -/
theorem Iew_nonneg (lam : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ ∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r) :=
  intervalIntegral.integral_nonneg hσ fun r hr =>
    mul_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg (by linarith [hr.2]) _))
      (Real.exp_pos _).le

/-- **The contraction constant**: for every `K ≥ 0` and `T ≥ 0` the exponential weight absorbs the
Volterra bound for a large `λ`. -/
theorem exists_lam {K : ℝ} (hK : 0 ≤ K) : ∃ lam : ℝ, 0 < lam ∧ ∀ σ ∈ Icc 0 T,
    K * (∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r)) ≤
      (1 / 2) * Real.exp (lam * σ) := by
  have hΓ : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  set A : ℝ := K * (1 + Real.sqrt T) * Real.Gamma (1 / 2) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(2 * A + 1) ^ 2, by positivity, fun σ hσ => ?_⟩
  set lam : ℝ := (2 * A + 1) ^ 2 with hlam
  have hlampos : 0 < lam := by positivity
  have hkey := UnforcedLeray.Infra.VolterraEvolution.integral_kernel_mul_exp_le (lam := lam)
    (s := 0) (τ := σ) hlampos hσ.1
  simp only [sub_zero] at hkey
  have hint1 : IntervalIntegrable (fun r : ℝ => (σ - r) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * r))
      volume 0 σ := by
    simpa using UnforcedLeray.Infra.VolterraEvolution.intervalIntegrable_kernel_mul_exp σ 0 lam 0 σ
  have hexp : Continuous fun r : ℝ => Real.exp (lam * r) := by fun_prop
  have hint2 : IntervalIntegrable (fun r : ℝ => (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r))
      volume 0 σ := by
    have h1 : IntervalIntegrable (fun r : ℝ => Real.exp (lam * r)) volume 0 σ :=
      hexp.intervalIntegrable _ _
    refine (h1.add hint1).congr fun r _ => ?_
    ring
  have hle : (∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r)) ≤
      ∫ r in (0 : ℝ)..σ, (1 + Real.sqrt T) * ((σ - r) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * r)) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hσ.1 hint2 (hint1.const_mul _) fun r hr => ?_
    have ht : 0 < σ - r := by linarith [hr.2]
    have hsq : 0 < Real.sqrt (σ - r) := Real.sqrt_pos.2 ht
    have hpow : (σ - r) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (σ - r))⁻¹ := by
      rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
    have hle1 : Real.sqrt (σ - r) ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith [hr.1, hσ.2])
    have h1 : 1 ≤ Real.sqrt T * (σ - r) ^ (-(1 / 2 : ℝ)) := by
      rw [hpow, ← div_eq_mul_inv, le_div_iff₀ hsq, one_mul]
      exact hle1
    have hE := Real.exp_pos (lam * r)
    have h2 : 1 + (σ - r) ^ (-(1 / 2 : ℝ)) ≤ (1 + Real.sqrt T) * (σ - r) ^ (-(1 / 2 : ℝ)) := by
      linarith
    calc (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r)
        ≤ ((1 + Real.sqrt T) * (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r) :=
          mul_le_mul_of_nonneg_right h2 hE.le
      _ = (1 + Real.sqrt T) * ((σ - r) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * r)) := by ring
  rw [intervalIntegral.integral_const_mul] at hle
  have hroot : (1 / lam) ^ (1 / 2 : ℝ) = 1 / (2 * A + 1) := by
    have hbase : 0 < 2 * A + 1 := by positivity
    rw [hlam, one_div, ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_sq hbase.le, one_div]
  rw [hroot] at hkey
  have hfrac : A / (2 * A + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hE := Real.exp_pos (lam * σ)
  calc K * (∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r))
      ≤ K * ((1 + Real.sqrt T) * ∫ r in (0 : ℝ)..σ, (σ - r) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * r)) :=
        mul_le_mul_of_nonneg_left hle hK
    _ ≤ K * ((1 + Real.sqrt T) * (1 / (2 * A + 1) * Real.Gamma (1 / 2) * Real.exp (lam * σ))) := by
        gcongr
    _ = A / (2 * A + 1) * Real.exp (lam * σ) := by
        rw [hA]
        field_simp
    _ ≤ (1 / 2) * Real.exp (lam * σ) := mul_le_mul_of_nonneg_right hfrac hE.le

/-! ## Order one: the Picard iteration in the class `{Z ∈ C¹_b : ψ Z ∈ C²_b}` -/

/-- **Order one.** If `y ∈ C¹_b`, `y = S - G[b·∇y]`, `S ∈ C¹_b` and `ψ S ∈ C²_b`, then `ψ y ∈ C²_b`
(`neumannX` for `A Z = -G[b·∇Z]`). -/
theorem levelOne_of (hG0 : GainZero) (hG1 : GainOne) (hC : CommGain) (hL : GLinear) {ν R R' : ℝ}
    {b0 b1 : ℝ → Pl → ℝ} {ψ : ℝ → ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hb0 : CB T 1 b0) (hb1 : CB T 1 b1)
    (hs0 : EtaS T R b0) (hs1 : EtaS T R b1) (hψ : IsCut R' ψ) {y S : ℝ → Pl → ℝ} (hy : CB T 1 y)
    (hS : CB T 1 S) (hψS : CB T 2 (mulC ψ S))
    (he : ∀ σ ∈ Icc 0 T, ∀ x : Pl, y σ x = S σ x - duhamelConv ν 0 (trm b0 b1 y) σ x) :
    CB T 2 (mulC ψ y) := by
  obtain ⟨K0, hK0, hgz⟩ := hG0 ν T R hν hT
  obtain ⟨K1, hK1, hgo⟩ := hG1 ν T (max R R') hν hT
  obtain ⟨KC, hKC, hgc⟩ := hC ν T R R' ψ hν hT hψ
  obtain ⟨M0, hM0, hb0M⟩ := CB.exists_le hb0
  obtain ⟨M1, hM1, hb1M⟩ := CB.exists_le hb1
  set Mb := M0 + M1 with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have hb0' : CBle T 1 b0 (fun _ => Mb) := CBle.mono_b hb0M fun _ _ => by linarith
  have hb1' : CBle T 1 b1 (fun _ => Mb) := CBle.mono_b hb1M fun _ _ => by linarith
  have hψ' : CB T 1 (cutF (deriv ψ)) := hψ.deriv.cb 1
  have hψ1 : CB T 1 (cutF ψ) := hψ.cb 1
  obtain ⟨Mψ, hMψ, hψM⟩ := CB.exists_le hψ'
  have hdψ : Differentiable ℝ ψ := hψ.differentiable
  set CF : ℝ := 2 * Mb + 2 * Mb + 2 * (2 * Mb * Mψ) with hCF
  have hCF0 : 0 ≤ CF := by positivity
  set Kt : ℝ := K0 * (2 * Mb) + KC * (2 * Mb) + K1 * CF with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  obtain ⟨lam, hlam, hlamle⟩ := exists_lam (T := T) hKt0
  -- the bound of the drift term
  have htrb : ∀ (Z : ℝ → Pl → ℝ) (M : ℝ), CBle T 1 Z (ew lam M) →
      CBle T 0 (trm b0 b1 Z) (ew lam (2 * Mb * M)) := by
    intro Z M hZ σ hσ x
    have h0 := CBle.top (hZ.2 0) σ hσ x
    have h1 := CBle.top (hZ.2 1) σ hσ x
    have h2 := hb0'.1 σ hσ x
    have h3 := hb1'.1 σ hσ x
    have hew : ew lam (2 * Mb * M) σ = Mb * ew lam M σ + Mb * ew lam M σ := by
      unfold ew
      ring
    rw [hew]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul h2 h0 (abs_nonneg _) hMb0
    · rw [abs_mul]
      exact mul_le_mul h3 h1 (abs_nonneg _) hMb0
  have hewc : ∀ M : ℝ, ContinuousOn (ew lam M) (Icc 0 T) := fun M =>
    (ew_continuous lam M).continuousOn
  have hew0 : ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ ew lam M r := fun M hM _ _ => ew_nonneg hM
  -- the size of `Kconv`
  have hKc : ∀ (K : ℝ) (C : ℝ) (M σ : ℝ), 0 ≤ K → 0 ≤ C → K * C ≤ Kt → 0 ≤ M → σ ∈ Icc 0 T →
      Kconv K (ew lam (C * M)) σ ≤ ew lam (M / 2) σ := by
    intro K C M σ hK hC hKC hM hσ
    rw [Kconv_ew]
    have hI := Iew_nonneg lam hσ.1
    have h1 := hlamle σ hσ
    have h2 : K * (C * M) *
        (∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r)) ≤
        M * (Kt * ∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r)) := by
      have : K * (C * M) = M * (K * C) := by ring
      rw [this, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKC hI) hM
    refine h2.trans ?_
    have h3 := mul_le_mul_of_nonneg_left h1 hM
    refine h3.trans (le_of_eq ?_)
    unfold ew
    ring
  refine neumannX (A := fun Z σ x => -duhamelConv ν 0 (trm b0 b1 Z) σ x) (lam := lam) hlam.le
    ?_ ?_ ?_ ?_ hy hS hψS ?_
  · -- additivity
    intro Z Z' hZ hZ' σ hσ x
    have h1 := trm_cb (CB.mono (Nat.zero_le 1) hb0) (CB.mono (Nat.zero_le 1) hb1) hZ
    have h2 := trm_cb (CB.mono (Nat.zero_le 1) hb0) (CB.mono (Nat.zero_le 1) hb1) hZ'
    have h3 := (hL ν T R _ _ 0 hν hT h1 h2 (trm_etaS Z hs0 hs1) (trm_etaS Z' hs0 hs1) σ hσ x).1
    have h4 := G_congr (T := T) (ν := ν) (F := trm b0 b1 (fun r y => Z r y + Z' r y))
      (F' := fun r y => trm b0 b1 Z r y + trm b0 b1 Z' r y)
      (fun r hr z => trm_add hZ hZ' r hr z) σ hσ x
    simp only [h4, h3]
    ring
  · -- homogeneity
    intro Z c hZ σ hσ x
    have h1 := trm_cb (CB.mono (Nat.zero_le 1) hb0) (CB.mono (Nat.zero_le 1) hb1) hZ
    have h3 := (hL ν T R _ _ c hν hT h1 h1 (trm_etaS Z hs0 hs1) (trm_etaS Z hs0 hs1) σ hσ x).2
    have h4 := G_congr (T := T) (ν := ν) (F := trm b0 b1 (fun r y => c * Z r y))
      (F' := fun r y => c * trm b0 b1 Z r y) (fun r hr z => trm_smul c hZ r hr z) σ hσ x
    simp only [h4, h3]
    ring
  · -- the `C¹_b` part
    intro Z M hM hZ hZb
    have hF : CB T 0 (trm b0 b1 Z) :=
      trm_cb (CB.mono (Nat.zero_le 1) hb0) (CB.mono (Nat.zero_le 1) hb1) hZ
    have hMM : 0 ≤ 2 * Mb * M := by positivity
    obtain ⟨g1, g2⟩ := hgz _ _ hF (trm_etaS Z hs0 hs1) (hewc _) (hew0 _ hMM) (htrb Z M hZb)
    refine ⟨CB.neg g1, CBle.mono_b (CBle.neg g2) fun σ hσ => ?_⟩
    refine hKc K0 (2 * Mb) M σ hK0 (by positivity) ?_ hM hσ
    have h1 : 0 ≤ KC * (2 * Mb) := by positivity
    have h2 : 0 ≤ K1 * CF := by positivity
    linarith
  · -- the `C²_b` part
    intro Z M hM hZ hZb hV hVb
    have hF : CB T 0 (trm b0 b1 Z) :=
      trm_cb (CB.mono (Nat.zero_le 1) hb0) (CB.mono (Nat.zero_le 1) hb1) hZ
    have hMM : 0 ≤ 2 * Mb * M := by positivity
    have hFs := trm_etaS (T := T) Z hs0 hs1
    obtain ⟨g1, g2⟩ := hgc _ _ hF hFs (hewc _) (hew0 _ hMM) (htrb Z M hZb)
    -- `ψ (b·∇Z)` is `C¹_b`
    have hFa : CB T 1 (trm b0 b1 (mulC ψ Z)) := trm_cb hb0 hb1 hV
    have hFb : CB T 1 (fun σ x => (b1 σ x * cutF (deriv ψ) σ x) * Z σ x) :=
      CB.mul (CB.mul hb1 hψ') hZ
    have hF1 : CB T 1 (mulC ψ (trm b0 b1 Z)) :=
      CB.congr (CB.sub hFa hFb) fun σ hσ x => (mulC_trm hdψ hZ σ hσ x).symm
    have hF1s : EtaS T (max R R') (mulC ψ (trm b0 b1 Z)) :=
      EtaS.mono (le_max_left _ _) (EtaS.mul_left _ hFs)
    -- its bound
    have hew0' : ∀ σ ∈ Icc 0 T, 0 ≤ ew lam M σ := fun σ _ => ew_nonneg hM
    have ha0 : CBle T 1 (fun σ x => b0 σ x * B0579.pd 0 (mulC ψ Z σ) x)
        (fun σ => 2 ^ 1 * Mb * ew lam M σ) :=
      CBle.mul hMb0 hew0' hb0 (hV.2.2 0) hb0' (hVb.2 0)
    have ha1 : CBle T 1 (fun σ x => b1 σ x * B0579.pd 1 (mulC ψ Z σ) x)
        (fun σ => 2 ^ 1 * Mb * ew lam M σ) :=
      CBle.mul hMb0 hew0' hb1 (hV.2.2 1) hb1' (hVb.2 1)
    have hab : CBle T 1 (fun σ x => b1 σ x * cutF (deriv ψ) σ x) (fun σ => 2 ^ 1 * Mb * Mψ) :=
      CBle.mul hMb0 (fun _ _ => hMψ) hb1 hψ' hb1' hψM
    have hac : CBle T 1 (fun σ x => (b1 σ x * cutF (deriv ψ) σ x) * Z σ x)
        (fun σ => 2 ^ 1 * (2 ^ 1 * Mb * Mψ) * ew lam M σ) :=
      CBle.mul (by positivity) hew0' (CB.mul hb1 hψ') hZ hab hZb
    have hF1b : CBle T 1 (mulC ψ (trm b0 b1 Z)) (ew lam (CF * M)) := by
      have h1 := CBle.add (CB.mul hb0 (hV.2.2 0)) (CB.mul hb1 (hV.2.2 1)) ha0 ha1
      have h2 := CBle.add hFa (CB.neg hFb) h1 (CBle.neg hac)
      refine CBle.mono_b (CBle.congr h2 fun σ hσ x => ?_) fun σ _ => le_of_eq ?_
      · rw [mulC_trm hdψ hZ σ hσ x]
        ring
      · unfold ew
        rw [hCF]
        ring
    have hCFM : 0 ≤ CF * M := by positivity
    obtain ⟨g3, g4, -⟩ := hgo _ _ hF1 hF1s (hewc _) (hew0 _ hCFM) hF1b
    -- the identity `ψ (A Z) = -([ψ, G] F + G (ψ F))`
    have hid : ∀ σ ∈ Icc 0 T, ∀ x : Pl,
        -(comm ν ψ (trm b0 b1 Z) σ x + duhamelConv ν 0 (mulC ψ (trm b0 b1 Z)) σ x) =
          mulC ψ (fun σ x => -duhamelConv ν 0 (trm b0 b1 Z) σ x) σ x := by
      intro σ _ x
      unfold comm mulC
      ring
    refine ⟨CB.congr (CB.neg (CB.add g1 g3)) hid, ?_⟩
    refine CBle.mono_b (CBle.congr (CBle.neg (CBle.add g1 g3 g2 g4)) hid) fun σ hσ => ?_
    have h1 : Kconv KC (ew lam (2 * Mb * M)) σ + Kconv K1 (ew lam (CF * M)) σ ≤
        ew lam (M / 2) σ := by
      rw [Kconv_ew, Kconv_ew]
      have hI := Iew_nonneg lam hσ.1
      have h1 := hlamle σ hσ
      have h3 := mul_le_mul_of_nonneg_left h1 hM
      set I := ∫ r in (0 : ℝ)..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * Real.exp (lam * r) with hIdef
      have h4 : KC * (2 * Mb * M) * I + K1 * (CF * M) * I ≤ M * (Kt * I) := by
        have h5 : 0 ≤ K0 * (2 * Mb) * M * I := by positivity
        rw [hKt]
        nlinarith
      refine h4.trans (h3.trans (le_of_eq ?_))
      unfold ew
      ring
    exact h1
  · -- the equation
    intro σ hσ x
    rw [he σ hσ x]
    ring

/-! ## Every order: differentiating the mild equation -/

theorem CB.mulC {R : ℝ} {m : ℕ} {ψ : ℝ → ℝ} {Z : ℝ → Pl → ℝ} (hψ : IsCut R ψ) (hZ : CB T m Z) :
    CB T m (mulC ψ Z) := CB.mul (hψ.cb m) hZ

theorem EtaS.sub {R : ℝ} {Z Z' : ℝ → Pl → ℝ} (h : EtaS T R Z) (h' : EtaS T R Z') :
    EtaS T R (fun σ x => Z σ x - Z' σ x) := fun σ hσ x hx => by
  simp [h σ hσ x hx, h' σ hσ x hx]

/-- **The gain of one derivative at every order**, by induction on the order: `∂_j` of the equation
for `y` is an equation of the same form for `∂_j y`, with one order less. -/
theorem gainStep_of (hG0 : GainZero) (hG1 : GainOne) (hC : CommGain) (hL : GLinear) {ν R R' Rp : ℝ}
    {b0 b1 : ℝ → Pl → ℝ} {ψ : ℝ → ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hb0 : ∀ m, CB T m b0)
    (hb1 : ∀ m, CB T m b1) (hs0 : EtaS T R b0) (hs1 : EtaS T R b1) (hψ : IsCut R' ψ)
    (hRp : R' < Rp) (m : ℕ) : ∀ (y S h p : ℝ → Pl → ℝ), CB T (m + 1) y → CB T (m + 1) S →
      CB T (m + 2) (mulC ψ S) → CB T (m + 1) h → EtaS T R h → CB T m p → EtaS T R p →
      OffBand T Rp p →
      (∀ σ ∈ Icc 0 T, ∀ x : Pl, y σ x = S σ x +
        duhamelConv ν 0 (fun r z => -trm b0 b1 y r z + h r z + p r z) σ x) →
      CB T (m + 2) (mulC ψ y) := by
  have hdψ : Differentiable ℝ ψ := hψ.differentiable
  induction m with
  | zero =>
      intro y S h p hy hS hψS hh hhs hp hps hpo he
      have hF : CB T 0 (trm b0 b1 y) := trm_cb (hb0 0) (hb1 0) hy
      have hFs := trm_etaS (T := T) y hs0 hs1
      obtain ⟨Mh, hMh, hhM⟩ := CB.exists_le hh
      obtain ⟨Mp, hMp, hpM⟩ := CB.exists_le hp
      obtain ⟨K1, -, hgo⟩ := hG1 ν T R hν hT
      obtain ⟨K0, -, hgz⟩ := hG0 ν T R hν hT
      obtain ⟨KC, -, hgc⟩ := hC ν T R R' ψ hν hT hψ
      obtain ⟨hGh, -, -⟩ := hgo h (fun _ => Mh) hh hhs continuousOn_const (fun _ _ => hMh) hhM
      obtain ⟨hGp, -⟩ := hgz p (fun _ => Mp) hp hps continuousOn_const (fun _ _ => hMp) hpM
      obtain ⟨hcp, -⟩ := hgc p (fun _ => Mp) hp hps continuousOn_const (fun _ _ => hMp) hpM
      have hψp : ∀ r ∈ Icc 0 T, ∀ z : Pl, mulC ψ p r z = (fun _ _ => (0 : ℝ)) r z := by
        intro r hr z
        show ψ z.2 * p r z = 0
        by_cases hz : |z.2| < Rp
        · rw [hpo r hr z hz, mul_zero]
        · rw [hψ.supp _ (lt_of_lt_of_le hRp (not_lt.1 hz)), zero_mul]
      have hcommp : ∀ σ ∈ Icc 0 T, ∀ x : Pl, comm ν ψ p σ x = ψ x.2 * duhamelConv ν 0 p σ x := by
        intro σ hσ x
        unfold comm
        rw [G_congr hψp σ hσ x, G_zero, sub_zero]
      refine levelOne_of hG0 hG1 hC hL (S := fun σ x => S σ x + duhamelConv ν 0 h σ x +
        duhamelConv ν 0 p σ x) hν hT (hb0 1) (hb1 1) hs0 hs1 hψ hy
        (CB.add (CB.add hS (CB.mono (by norm_num) hGh)) hGp) ?_ ?_
      · have h1 := CB.add (CB.add hψS (CB.mulC hψ hGh)) hcp
        refine CB.congr h1 fun σ hσ x => ?_
        show ψ x.2 * S σ x + ψ x.2 * duhamelConv ν 0 h σ x + comm ν ψ p σ x =
          ψ x.2 * (S σ x + duhamelConv ν 0 h σ x + duhamelConv ν 0 p σ x)
        rw [hcommp σ hσ x]
        ring
      · intro σ hσ x
        have hneg : (fun r z => -trm b0 b1 y r z) = fun r z => (-1) * trm b0 b1 y r z :=
          funext fun r => funext fun z => by ring
        have hF' : CB T 0 (fun r z => -trm b0 b1 y r z) := CB.neg hF
        have hFs' : EtaS T R (fun r z => -trm b0 b1 y r z) := EtaS.neg hFs
        have e1 := (hL ν T R (fun r z => -trm b0 b1 y r z + h r z) p 0 hν hT
          (CB.add hF' (CB.mono (by norm_num) hh)) hp (EtaS.add hFs' hhs) hps σ hσ x).1
        have e2 := (hL ν T R (fun r z => -trm b0 b1 y r z) h 0 hν hT hF'
          (CB.mono (by norm_num) hh) hFs' hhs σ hσ x).1
        have e3 := (hL ν T R (trm b0 b1 y) (trm b0 b1 y) (-1) hν hT hF hF hFs hFs σ hσ x).2
        rw [← hneg] at e3
        rw [he σ hσ x, e1, e2, e3]
        ring
  | succ m ih =>
      intro y S h p hy hS hψS hh hhs hp hps hpo he
      -- the integrand and its derivative
      have hFt : CB T (m + 1) (trm b0 b1 y) := trm_cb (hb0 _) (hb1 _) hy
      have hFs := trm_etaS (T := T) y hs0 hs1
      have hh' : CB T (m + 1) h := CB.mono (by omega) hh
      let Q : ℝ → Pl → ℝ := fun r z => -trm b0 b1 y r z + h r z + p r z
      have hQ : CB T (m + 1) Q := CB.add (CB.add (CB.neg hFt) hh') hp
      have hQs : EtaS T R Q := EtaS.add (EtaS.add (EtaS.neg hFs) hhs) hps
      obtain ⟨MQ, hMQ, hQM⟩ := CB.exists_le (CB.mono (by omega : 1 ≤ m + 1) hQ)
      obtain ⟨K1, -, hgo⟩ := hG1 ν T R hν hT
      obtain ⟨hGQ, -, hGQd⟩ := hgo Q (fun _ => MQ) (CB.mono (by omega) hQ) hQs continuousOn_const
        (fun _ _ => hMQ) hQM
      -- the differentiated data
      have hC2 : ∀ r ∈ Icc 0 T, ContDiff ℝ 2 (y r) := fun r hr => by
        have := CB.contDiff (CB.mono (by omega : 2 ≤ m + 1 + 1) hy) r hr
        exact_mod_cast this
      refine ⟨(CB.mulC hψ hy).cb0, (CB.mulC hψ hy).2.1, fun j => ?_⟩
      have hb0j : CB T (m + 1) (fun σ => B0579.pd j (b0 σ)) := (hb0 (m + 2)).2.2 j
      have hb1j : CB T (m + 1) (fun σ => B0579.pd j (b1 σ)) := (hb1 (m + 2)).2.2 j
      have hhj : CB T (m + 1) (fun σ x => B0579.pd j (h σ) x -
          trm (fun σ => B0579.pd j (b0 σ)) (fun σ => B0579.pd j (b1 σ)) y σ x) :=
        CB.sub (hh.2.2 j) (trm_cb hb0j hb1j hy)
      have hhjs : EtaS T R (fun σ x => B0579.pd j (h σ) x -
          trm (fun σ => B0579.pd j (b0 σ)) (fun σ => B0579.pd j (b1 σ)) y σ x) :=
        EtaS.sub (hhs.pd j) (trm_etaS y (hs0.pd j) (hs1.pd j))
      have hψSj : CB T (m + 2) (mulC ψ (fun σ => B0579.pd j (S σ))) := by
        refine CB.congr (CB.sub (hψS.2.2 j) (CB.mul ((hψ.dCut j).cb (m + 2)) hS)) fun σ hσ x => ?_
        show B0579.pd j (fun y => ψ y.2 * S σ y) x - dCut ψ j x.2 * S σ x = _
        rw [pd_mulC hdψ (hS.2.1 σ hσ x) j]
        simp only [mulC]
        ring
      -- the differentiated equation
      have hej : ∀ σ ∈ Icc 0 T, ∀ x : Pl, B0579.pd j (y σ) x = B0579.pd j (S σ) x +
          duhamelConv ν 0 (fun r z =>
            -trm b0 b1 (fun σ => B0579.pd j (y σ)) r z +
              (B0579.pd j (h r) z -
                trm (fun σ => B0579.pd j (b0 σ)) (fun σ => B0579.pd j (b1 σ)) y r z) +
              B0579.pd j (p r) z) σ x := by
        intro σ hσ x
        have hfun : y σ = fun z => S σ z + duhamelConv ν 0 Q σ z := funext (he σ hσ)
        have h1 : B0579.pd j (y σ) x = B0579.pd j (S σ) x + B0579.pd j (duhamelConv ν 0 Q σ) x := by
          rw [hfun]
          exact pd_add j (hS.2.1 σ hσ x) (hGQ.2.1 σ hσ x)
        rw [h1, hGQd σ hσ j x]
        congr 1
        refine G_congr (fun r hr z => ?_) σ hσ x
        -- `∂_j Q`
        have hd0 := hb0 1
        have hd1 := hb1 1
        have hpy0 : DifferentiableAt ℝ (B0579.pd 0 (y r)) z := (hy.2.2 0).2.1 r hr z
        have hpy1 : DifferentiableAt ℝ (B0579.pd 1 (y r)) z := (hy.2.2 1).2.1 r hr z
        have hb0d : DifferentiableAt ℝ (b0 r) z := hd0.2.1 r hr z
        have hb1d : DifferentiableAt ℝ (b1 r) z := hd1.2.1 r hr z
        have hA0 : DifferentiableAt ℝ (fun w => b0 r w * B0579.pd 0 (y r) w) z := hb0d.mul hpy0
        have hA1 : DifferentiableAt ℝ (fun w => b1 r w * B0579.pd 1 (y r) w) z := hb1d.mul hpy1
        have hTd : DifferentiableAt ℝ (fun w => trm b0 b1 y r w) z := hA0.add hA1
        have hhd : DifferentiableAt ℝ (h r) z := hh.2.1 r hr z
        have hpd : DifferentiableAt ℝ (p r) z := hp.2.1 r hr z
        have hQr : Q r = fun w => (fun w => -trm b0 b1 y r w + h r w) w + p r w := rfl
        have hneg : B0579.pd j (fun w => -trm b0 b1 y r w) z = -B0579.pd j (trm b0 b1 y r) z := by
          unfold B0579.pd
          rw [fderiv_fun_neg]
          rfl
        have htrm : B0579.pd j (trm b0 b1 y r) z =
            b0 r z * B0579.pd j (B0579.pd 0 (y r)) z + B0579.pd 0 (y r) z * B0579.pd j (b0 r) z +
            (b1 r z * B0579.pd j (B0579.pd 1 (y r)) z +
              B0579.pd 1 (y r) z * B0579.pd j (b1 r) z) := by
          have e : trm b0 b1 y r = fun w => b0 r w * B0579.pd 0 (y r) w +
              b1 r w * B0579.pd 1 (y r) w := rfl
          rw [e, pd_add j hA0 hA1, pd_mul j hb0d hpy0, pd_mul j hb1d hpy1]
        have hadd1 := pd_add j (f := fun w => -trm b0 b1 y r w + h r w) (g := p r) (x := z)
          (hTd.neg.add hhd) hpd
        have hadd2 := pd_add j (f := fun w => -trm b0 b1 y r w) (g := h r) (x := z) hTd.neg hhd
        show B0579.pd j (Q r) z = _
        rw [hQr, hadd1, hadd2, hneg, htrm,
          pd_comm_of_contDiff (hC2 r hr) j 0 z, pd_comm_of_contDiff (hC2 r hr) j 1 z]
        simp only [trm]
        ring
      have hrec := ih (fun σ => B0579.pd j (y σ)) (fun σ => B0579.pd j (S σ)) _
        (fun σ => B0579.pd j (p σ)) (hy.2.2 j) (hS.2.2 j) hψSj hhj hhjs (hp.2.2 j) (hps.pd j)
        (hpo.pd j) hej
      -- back to `∂_j (ψ y)`
      refine CB.congr (CB.add hrec (CB.mul ((hψ.dCut j).cb (m + 2)) hy)) fun σ hσ x => ?_
      show ψ x.2 * B0579.pd j (y σ) x + dCut ψ j x.2 * y σ x = B0579.pd j (fun y' => ψ y'.2 * y σ y') x
      rw [pd_mulC hdψ (hy.2.1 σ hσ x) j]
      ring

/-! ## The Laplacian of a cutoff -/

theorem lapP_cut {ψ : ℝ → ℝ} {R : ℝ} (hψ : IsCut R ψ) (x : Pl) :
    lapP (fun y : Pl => ψ y.2) x = deriv (deriv ψ) x.2 := by
  have hd := hψ.differentiable
  have hd' := hψ.deriv.differentiable
  have h0 : B0579.pd 0 (fun y : Pl => ψ y.2) = fun _ => 0 := funext fun y => by
    rw [pd_cut hd, dCut_zero]
  have h1 : B0579.pd 1 (fun y : Pl => ψ y.2) = fun y : Pl => deriv ψ y.2 := funext fun y => by
    rw [pd_cut hd, dCut_one]
  unfold lapP
  rw [h0, h1, pd_const, pd_cut hd', dCut_one, zero_add]

/-! ## The local equation and the assembly -/

theorem locStep_of (hA : TruncDrift) (hB : FreeCB) (hL : GLinear) (hG0 : GainZero) (hG1 : GainOne)
    (hC : CommGain) (hM : ClassicalToMild) : LocStep := by
  intro c ν T w f u hd k hk ρ hloc
  by_cases hρ : 0 < ρ
  swap
  · -- the band is empty
    have hempty : band ρ = ∅ := by
      ext x
      simp only [band, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (not_lt.1 hρ).trans (abs_nonneg _)
    refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun _ _ => ⟨0, fun _ _ x hx => ?_⟩⟩
    · rw [hempty]
      exact contDiffOn_empty
    · rw [hempty]
      simp
    · rw [hempty] at hx
      exact absurd hx (notMem_empty _)
  have hν := hd.hν
  have hT := hd.hT
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : 1 ≤ k' := by omega
  obtain ⟨θ, hθ, hθ1⟩ := exists_cut (R₁ := ρ + 5 / 2) (R₂ := ρ + 3) (by linarith) (by linarith)
  obtain ⟨ψ, hψ, hψ1⟩ := exists_cut (R₁ := ρ + 1) (R₂ := ρ + 2) (by linarith) (by linarith)
  obtain ⟨φ, hφ, hφ1⟩ := exists_cut (R₁ := ρ) (R₂ := ρ + 1 / 2) hρ (by linarith)
  have hψd := hψ.differentiable
  -- the truncated drift
  let wi : Fin 2 → ℝ → Pl → ℝ := fun i σ x => w σ x i
  have hwi : ∀ (i : Fin 2) (m : ℕ), CB T m (mulC θ (wi i)) := by
    intro i m
    refine hA c T (ρ + 3) (wi i) θ hd.hc ?_ (fun σ hσ x => ?_) hθ m
    · exact (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn
        hd.smooth
    · show w σ (x.1 + c, x.2) i = w σ x i
      rw [hd.coeff.periodic σ hσ x]
  set b0 := mulC θ (wi 0) with hb0def
  set b1 := mulC θ (wi 1) with hb1def
  have hs0 : EtaS T (ρ + 3) b0 := fun σ _ x hx => by simp [hb0def, mulC, hθ.supp _ hx]
  have hs1 : EtaS T (ρ + 3) b1 := fun σ _ x hx => by simp [hb1def, mulC, hθ.supp _ hx]
  -- `Y = ψ u`
  have hcbl : CBL T (ρ + 3) (k' + 1) u := locCk_cbl hloc
  have hR : ρ + 2 < ρ + 3 := by linarith
  set Y := mulC ψ u with hYdef
  have hY : CB T (k' + 1) Y := CBL.cut hR (k' + 1) hψ hcbl
  have hYs : EtaS T (ρ + 3) Y := fun σ _ x hx => by
    have : ρ + 2 < |x.2| := by linarith
    simp [hYdef, mulC, hψ.supp _ this]
  -- the forcing `g`
  let g : ℝ → Pl → ℝ := fun σ x => (-2 * ν) * (deriv ψ x.2 * B0579.pd 1 (u σ) x) +
    (-ν) * (deriv (deriv ψ) x.2 * u σ x) + b1 σ x * (deriv ψ x.2 * u σ x)
  have hg1 : CB T k' (mulC (deriv ψ) (fun σ => B0579.pd 1 (u σ))) :=
    CBL.cut hR k' hψ.deriv (hcbl.2.2 1)
  have hg2 : CB T k' (mulC (deriv (deriv ψ)) u) :=
    CBL.cut hR k' hψ.deriv.deriv (CBL.mono (by omega) hcbl)
  have hg3 : CB T k' (mulC (deriv ψ) u) := CBL.cut hR k' hψ.deriv (CBL.mono (by omega) hcbl)
  have hg : CB T k' g :=
    CB.add (CB.add (CB.const_mul _ hg1) (CB.const_mul _ hg2)) (CB.mul (hwi 1 k') hg3)
  have hdψ0 : ∀ t : ℝ, ρ + 2 < |t| → deriv ψ t = 0 := fun t ht => hψ.deriv.supp t ht
  have hddψ0 : ∀ t : ℝ, ρ + 2 < |t| → deriv (deriv ψ) t = 0 := fun t ht => hψ.deriv.deriv.supp t ht
  have hgs : EtaS T (ρ + 3) g := fun σ _ x hx => by
    have hx' : ρ + 2 < |x.2| := by linarith
    simp [g, hdψ0 _ hx', hddψ0 _ hx']
  have hgo : OffBand T (ρ + 1) g := fun σ _ x hx => by
    have h1 : deriv ψ x.2 = 0 := deriv_eq_zero_of_plateau hψ1 hx
    have h2 : deriv (deriv ψ) x.2 = 0 := by
      have hU : IsOpen {s : ℝ | |s| < ρ + 1} := isOpen_lt continuous_abs continuous_const
      have hev : deriv ψ =ᶠ[𝓝 x.2] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hU.mem_nhds hx) fun s hs => deriv_eq_zero_of_plateau hψ1 hs
      rw [hev.deriv_eq]
      simp
    simp [g, h1, h2]
  -- the integrand of the mild equation
  let F : ℝ → Pl → ℝ := fun σ x => -trm b0 b1 Y σ x + g σ x
  have hF0 : CB T 0 F :=
    CB.add (CB.neg (trm_cb (hwi 0 0) (hwi 1 0) (CB.mono (by omega) hY))) (CB.mono (Nat.zero_le _) hg)
  have hFs : EtaS T (ρ + 3) F := EtaS.add (EtaS.neg (trm_etaS Y hs0 hs1)) hgs
  -- the classical equation of `Y`
  obtain ⟨B, hBc⟩ := hd.mild.cls
  have hpde : ∀ σ ∈ Icc 0 T, ∀ x : Pl,
      HasDerivWithinAt (fun r => Y r x) (ν * lapP (Y σ) x + F σ x) (Icc 0 T) σ := by
    intro σ hσ x
    have hp := (hd.pde σ hσ x).const_mul (ψ x.2)
    refine hp.congr_deriv ?_
    have hc2 : ContDiff ℝ 2 (u σ) := hBc.c2 σ hσ
    have hud : DifferentiableAt ℝ (u σ) x := hc2.differentiable (by norm_num) x
    have hcut2 : ContDiff ℝ 2 (fun y : Pl => ψ y.2) :=
      (hψ.smooth.of_le (by simp)).comp contDiff_snd
    have hlap := lapPMul (fun y : Pl => ψ y.2) (u σ) x hcut2 hc2
    rw [lapP_cut hψ, pd_cut hψd, pd_cut hψd, dCut_zero, dCut_one] at hlap
    have hY0 := pd_mulC (x := x) hψd hud 0
    have hY1 := pd_mulC (x := x) hψd hud 1
    rw [dCut_zero] at hY0
    rw [dCut_one] at hY1
    have hYσ : Y σ = fun y : Pl => ψ y.2 * u σ y := rfl
    have hθψ : θ x.2 * ψ x.2 = ψ x.2 := by
      by_cases hx : |x.2| ≤ ρ + 5 / 2
      · rw [hθ1 _ hx, one_mul]
      · have : ρ + 2 < |x.2| := by linarith [not_le.1 hx]
        rw [hψ.supp _ this, mul_zero]
    simp only [F, g, trm]
    rw [hYσ, hlap, hY0, hY1]
    simp only [hb0def, hb1def, mulC, wi]
    generalize B0579.pd 0 (u σ) x = P0
    generalize B0579.pd 1 (u σ) x = P1
    generalize lapP (u σ) x = Lu
    generalize deriv (deriv ψ) x.2 = a2
    generalize deriv ψ x.2 = a1
    generalize u σ x = U
    generalize w σ x 0 = w0
    generalize w σ x 1 = w1
    generalize ψ x.2 = a at hθψ ⊢
    generalize θ x.2 = t at hθψ ⊢
    linear_combination (w0 * P0 + w1 * P1) * hθψ
  -- Duhamel's formula for `Y`
  have hmild := hM ν T (ρ + 3) Y F hν hT (CB.mono (by omega) hY) hYs hF0 hFs hpde
  -- the datum
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hu0 : u 0 = f := by
    funext x
    have h := hd.mild.duhamel 0 hT0 x
    simp only [duhamelMap, duhamelConv, heatSG, sub_self, mul_zero, le_refl, ↓reduceIte,
      intervalIntegral.integral_same, sub_zero] at h
    exact h
  let f₀ : Pl → ℝ := fun x => ψ x.2 * f x
  have hY0 : Y 0 = f₀ := by
    funext x
    show ψ x.2 * u 0 x = ψ x.2 * f x
    rw [hu0]
  have hf₀ : B0579.IsCylTest c f₀ := by
    refine ⟨(hψ.smooth.comp contDiff_snd).mul hd.datum.smooth, fun x => ?_, ?_⟩
    · show ψ x.2 * f (x.1 + c, x.2) = ψ x.2 * f x
      rw [hd.datum.periodic x]
    · refine ⟨ρ + 2, fun x hx => ?_⟩
      show ψ x.2 * f x = 0
      rw [hψ.supp _ hx, zero_mul]
  have hS := hB c ν T f₀ hd.hc hν hT hf₀
  -- the gain
  have hrec := gainStep_of hG0 hG1 hC hL (ν := ν) (R := ρ + 3) (R' := ρ + 1 / 2) (Rp := ρ + 1)
    (b0 := b0) (b1 := b1) (ψ := φ) hν hT (hwi 0) (hwi 1) hs0 hs1 hφ (by linarith) k' Y
    (fun σ => heatSG (ν * σ) f₀) (fun _ _ => 0) g hY (hS _) (CB.mulC hφ (hS _)) (CB.const _ 0)
    (fun _ _ _ _ => rfl) hg hgs hgo ?_
  · refine locCk_of_CB hrec fun σ _ x hx => ?_
    have hx0 : |x.2| ≤ ρ := le_of_lt hx
    show φ x.2 * (ψ x.2 * u σ x) = u σ x
    rw [hφ1 _ hx0, hψ1 _ (by linarith), one_mul, one_mul]
  · intro σ hσ x
    rw [hmild σ hσ x, hY0]
    congr 1
    refine G_congr (fun r _ z => ?_) σ hσ x
    simp only [F]
    ring

end LS

end UnforcedLeray.Short.IIb.BwdRoute
