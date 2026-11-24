import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/8/2/2`: the mean jet estimates `MeanJet`, decomposed

Source `the November 2 reference manuscript`
5438-5448 (mean transverse Taylor and Hessian estimates), 5380-5387 (`X^mt`, `Y^mt = D_{μ+1}X^mt`),
5400-5413 (gradient Newton kernel degree `-5`, old/young radius ratio `≤ 1/√1.2`).

`MeanJetAt` is the conjunction of three pointwise statements.  The analytic content is

* `MeanXHessAt`, `MeanYHessAt` : the Hessian bounds `‖D²_y X^mt‖, ‖D²_y Y^mt‖ ≤ P_ν ε⁴ s³ N`
  at the receiver `y = (R/√s, 0, η/√s)`, `0 < s ≤ 1/ν` (kernel degree `-5` for `D_y X`, one more
  derivative for `D²`; `Y^mt` has two further derivatives, each costing degree one with the factor
  `r` of `s∂_s`; the old/young radius ratio is `≤ 1/√1.2` so the gap is uniform);
* `MeanSmoothAt` : `X^mt = Xmt` is `C⁴` at every such receiver point (the Newton response of a
  source supported at ages `≥ 1.2/ν` is smooth at the young receiver; the stream cutoff is smooth).

From these, the Taylor estimates `MeanXTaylorAt`, `MeanYTaylorAt` follow by Taylor's formula along
the vertical segment of constant radius (hence constant age `s`, so the Hessian bound applies at
every point of the segment) of length `|η|/√s`, using that at `η = 0` the columns are exactly
`LjFun` and `s·Bjet`.  `meanJet_of` assembles the three pieces.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

section Hyp

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **X-Taylor** (first conjunct of `MeanJetAt`, source 5438-5443). -/
def MeanXTaylorAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ∀ j : Fin 3,
      ‖physPd (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j
          (NearInst.chartY L.ε⁻¹ p) -
        vecSp (fun i => LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T
          p.1 i j)‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * |p.2.2|) *
        oldN1 Pl K L T

/-- **Y-Taylor** (second conjunct of `MeanJetAt`, source 5438-5443). -/
def MeanYTaylorAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ∀ j : Fin 3,
      ‖physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j
          (NearInst.chartY L.ε⁻¹ p) -
        p.1 • vecSp (fun i => Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 i j)‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * |p.2.2|) *
        oldN1 Pl K L T

/-- **X-Hessian** (third conjunct of `MeanJetAt`, source 5445-5447). -/
def MeanXHessAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ∀ j l : Fin 3,
      ‖physPd2 (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j l
          (NearInst.chartY L.ε⁻¹ p)‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (3 : ℝ)) * oldN1 Pl K L T

/-- **Y-Hessian**: the same bound for `Y^mt = D_{μ+1}X^mt` (needed for the Taylor estimate of
`Y^mt`, source 5441-5443: the displayed bound for `D_yY^mt` along the vertical segment). -/
def MeanYHessAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ∀ j l : Fin 3,
      ‖physPd2 (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j l
          (NearInst.chartY L.ε⁻¹ p)‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (3 : ℝ)) * oldN1 Pl K L T

/-- **Smoothness of the mean Newton field at the young receivers** (so that `physPd`, `physPd2`
of `Xmean`, `Ymean` are honest derivatives and Taylor's formula applies). -/
def MeanSmoothAt : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ContDiffAt ℝ 4 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
      (WithLp.ofLp (NearInst.chartY L.ε⁻¹ p))

end Hyp

namespace SeqData

variable (D : SeqData)

/-- Sequence-level `MeanXTaylorAt`. -/
def MeanXTaylorSeq (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanXTaylorAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence-level `MeanYTaylorAt`. -/
def MeanYTaylorSeq (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanYTaylorAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence-level `MeanXHessAt`. -/
def MeanXHessSeq (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanXHessAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence-level `MeanYHessAt`. -/
def MeanYHessSeq (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanYHessAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence-level `MeanSmoothAt`. -/
def MeanSmoothSeq (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanSmoothAt D.Pl D.K (D.level n) (D.mu n z)

end SeqData

theorem bump_const {Ci C Ni N R : ℝ} (hC : |Ci| ≤ C) (hN : Ni ≤ N) (hN0 : 0 ≤ Ni) (hR : 0 ≤ R) :
    Ci * Ni * R ≤ C * N * R := by
  have h1 : Ci * Ni ≤ C * N := by
    calc Ci * Ni ≤ |Ci| * Ni := mul_le_mul_of_nonneg_right (le_abs_self _) hN0
      _ ≤ C * N := mul_le_mul hC hN hN0 ((abs_nonneg _).trans hC)
  exact mul_le_mul_of_nonneg_right h1 hR

theorem bump5 {Ci C Ni N E S H : ℝ} (hC : |Ci| ≤ C) (hN : Ni ≤ N) (hN0 : 0 ≤ Ni) (hE : 0 ≤ E)
    (hS : 0 ≤ S) (hH : 0 ≤ H) : Ci * Ni * E * S * H ≤ C * N * E * S * H := by
  have := bump_const hC hN hN0 (mul_nonneg (mul_nonneg hE hS) hH)
  calc Ci * Ni * E * S * H = Ci * Ni * (E * S * H) := by ring
    _ ≤ C * N * (E * S * H) := this
    _ = C * N * E * S * H := by ring

theorem bump4 {Ci C Ni N E S : ℝ} (hC : |Ci| ≤ C) (hN : Ni ≤ N) (hN0 : 0 ≤ Ni) (hE : 0 ≤ E)
    (hS : 0 ≤ S) : Ci * Ni * E * S ≤ C * N * E * S := by
  have := bump_const hC hN hN0 (mul_nonneg hE hS)
  calc Ci * Ni * E * S = Ci * Ni * (E * S) := by ring
    _ ≤ C * N * (E * S) := this
    _ = C * N * E * S := by ring

/-- `MeanJet` from the Taylor and Hessian estimates (constants and exponents combined, using
`ν ≤ 1` for large `n`). -/
theorem meanJet_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hX : D.MeanXTaylorSeq dm dp) (hY : D.MeanYTaylorSeq dm dp) (hH : D.MeanXHessSeq dm dp) :
    D.MeanJet := by
  obtain ⟨C1, k1, e1⟩ := hX hst
  obtain ⟨C2, k2, e2⟩ := hY hst
  obtain ⟨C3, k3, e3⟩ := hH hst
  have hle := retNu_retEps_eventually_le_one (Pl := D.Pl) (σ₀ := D.σ₀) hst.omega_ne
    hst.gamma_pos D.coeff_ne
  refine ⟨max (max |C1| |C2|) |C3|, max k1 (max k2 k3), ?_⟩
  filter_upwards [e1, e2, e3, hle] with n a b c hn z hz T p h0 h1
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν1 : (D.level n).ν ≤ 1 := hn.1
  have hinv : 1 ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hpow : ∀ ki : ℕ, ki ≤ max k1 (max k2 k3) →
      (D.level n).ν⁻¹ ^ ki ≤ (D.level n).ν⁻¹ ^ (max k1 (max k2 k3)) :=
    fun ki h => pow_le_pow_right₀ hinv h
  have hN0 : ∀ ki : ℕ, 0 ≤ (D.level n).ν⁻¹ ^ ki := fun ki => by positivity
  have hE : 0 ≤ (D.level n).ε ^ 4 := by positivity
  have hS5 : 0 ≤ p.1 ^ (5 / 2 : ℝ) := Real.rpow_nonneg h0.le _
  have hS3 : 0 ≤ p.1 ^ (3 : ℝ) := Real.rpow_nonneg h0.le _
  have hH0 : 0 ≤ |p.2.2| := abs_nonneg _
  have m1 : |C1| ≤ max (max |C1| |C2|) |C3| := le_trans (le_max_left _ _) (le_max_left _ _)
  have m2 : |C2| ≤ max (max |C1| |C2|) |C3| := le_trans (le_max_right _ _) (le_max_left _ _)
  have m3 : |C3| ≤ max (max |C1| |C2|) |C3| := le_max_right _ _
  refine ⟨fun j => ?_, fun j => ?_, fun j l => ?_⟩
  · exact (a z hz T p h0 h1 j).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (bump5 m1 (hpow k1 (le_max_left _ _)) (hN0 k1) hE hS5 hH0)) le_rfl)
  · exact (b z hz T p h0 h1 j).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (bump5 m2 (hpow k2 (le_trans (le_max_left _ _) (le_max_right _ _))) (hN0 k2) hE hS5 hH0))
      le_rfl)
  · exact (c z hz T p h0 h1 j l).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (bump4 m3 (hpow k3 (le_trans (le_max_right _ _) (le_max_right _ _))) (hN0 k3) hE hS3))
      le_rfl)

end UnforcedLeray.Short.PartIIIb.Concrete
end
