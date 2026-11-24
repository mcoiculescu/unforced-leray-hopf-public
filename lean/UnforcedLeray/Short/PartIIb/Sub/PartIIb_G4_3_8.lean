import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7

/-!
# Part II-b, task `PartII-b:G4/3/8` (`ColumnDifference`): decomposition

Source of record: `the November 2 reference manuscript` (SP), lines 2360-2379
(`𝒞_ε - 𝒞_0 = εsr_ε`, `r_ε` smooth at zero, compact in upper age, polynomial weighted bounds).

With `e_ε = e_0 + εe_1` (`InletSplit`), the column difference on `s > 0` is
`s[ε∂_se_1 - ν(L_εe_ε - Δe_0) + B_εe_ε - B_0e_0]` (`DiffReal`, with the real flat column
`flatReal`), every term carrying an explicit factor `ε`. Then `ColWeightNorm` (shared with
`ColumnMem`, file `PartII-b_G4_3_7`) turns the envelope into the `H_p` bound.

Proved here: `inletSplit`, `columnDifference_of_parts`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- `e_1 = (0, φ - 2sφ_s - ηφ_η)` with `φ = cutStream i` (SP 2360-2366). -/
def inletE1 (p : Params) (i : Fin 2) : Coord → Axi.Merid := fun m =>
  (p.cutStream i m - 2 * m.1 * Axi.dS (p.cutStream i) m - m.2.2 * Axi.dEta (p.cutStream i) m) •
    Axi.m1

/-- `e_ε = e_0 + εe_1` (SP 2360-2366; `ringStreamProfile R φ` with `R⁻¹ = ε`). -/
theorem inletSplit (p : Params) (i : Fin 2) :
    p.inletProfile i = fun x => inletE0 p i x + p.ε • inletE1 p i x := by
  funext x
  have hR : p.R⁻¹ = p.ε := by simp [Params.R]
  simp only [Params.inletProfile, Axi.ringStreamProfile, hR, inletE0, inletE1, smul_smul,
    add_smul]
  rw [add_assoc]

/-- **Joint differentiability of the train and the raised stream on `s > 0`** (SP 397, 2049:
`BgRegime.train_stream_smooth` for `ψ`, hence for `H = (1 - K)ψ`; the train velocity `v` is smooth in
`(s, z)` on `s > 0`, `IsClassicalOn.smooth_v` via `trainSol_isClassicalOn` of `BgRegime.train_buc`'s
train). Needed to identify the partial derivatives in `flatK` with `Axi.dQ`, `Axi.dEta`. -/
def TrainDiff : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → ∀ x : Coord, 0 < x.1 →
    DifferentiableAt ℝ (trainProf p) x ∧ DifferentiableAt ℝ (raisedMerid p) x

/-- The flat interaction `B_0F = (v·∇)F + (F·∇)v` in the chart (`ε = 0` in `bEps`, with the train
`v = trainProf` in place of `b_raw`). -/
def flatB (p : Params) (F : Coord → Axi.Merid) (x : Coord) : Axi.Merid :=
  trainProf p x 0 • Axi.dQ F x + trainProf p x 1 • Axi.dEta F x +
    (F x 0 • Axi.dQ (trainProf p) x + F x 1 • Axi.dEta (trainProf p) x)

/-- The real flat column `s[(∂_s - νΔ)e_0 + B_0e_0]` (SP 2370-2382, `ε = 0`). -/
def flatReal (p : Params) (i : Fin 2) (x : Coord) : Axi.Merid :=
  x.1 • (Axi.dS (inletE0 p i) x - p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) x +
    Axi.dEta (Axi.dEta (inletE0 p i)) x) + flatB p (inletE0 p i) x)

/-- **`flatColumn` is the lift of `flatReal`** on `s > 0` (`flatK` uses the partial derivatives
`∂_z (tr.v s z)` in the plane variable `z = (q, η)`; these equal the chart derivatives
`Axi.dQ`, `Axi.dEta` of `trainProf` because `v` is jointly smooth on `s > 0`
(`BgRegime.train_stream_smooth`, `IsClassicalOn.smooth_v`, `trainSol_isClassicalOn`)). -/
def FlatColumnReal : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      ∀ x : Coord, 0 < x.1 → flatColumn p i x = cplx (flatReal p i) x

/-- **The flat column vanishes beyond the cutoff** (`e_0` is built from `cutStream`, which vanishes
on the open set `s > H/2`). -/
def FlatColVanish : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      ∀ x : Coord, p.H / 2 < x.1 → flatColumn p i x = 0

/-- **Jets of `e_0` and `e_1` with transverse decay** (SP 2360-2366; from `cutStreamJets` with
`j + 1`, the cutoff derivatives `(1+H⁻¹)^j`, `s ≤ H` and `|η|e^{-κ|η|/c} ≤ (2c/κ)e^{-κ|η|/(2c)}`):
both are `C^∞` and their jets of order `≤ j` on `s ≤ H` are `≤ Cν^{-k}(1+|η|)^Ne^{-κ|η|/c}`. -/
def InletComponentJets : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∀ j : ℕ, ∃ (C κ : ℝ) (k N : ℕ) (ν₀ : ℝ),
    0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      ContDiff ℝ ∞ (inletE0 p i) ∧ ContDiff ℝ ∞ (inletE1 p i) ∧
      ∀ l ≤ j, ∀ x : Coord, x.1 ≤ p.H →
        ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ + ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ ≤
          C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N * Real.exp (-(κ * |x.2.2| / p.c))

/-- **`L_ε` is `Δ` up to `O(ε)`** (pure calculus): for `C^∞` `F` and `0 ≤ ε ≤ 1`,
`‖L_εF - (∂_q²F + ∂_η²F)‖ ≤ εK(1+|s|+|η|)²Σ_{l≤2}‖D^lF‖`. -/
def VecDiffFlat : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 → ∀ (F : Coord → Axi.Merid), ContDiff ℝ ∞ F →
    ∀ x : Coord,
      ‖vecDiffEps ε F x - (Axi.dQ (Axi.dQ F) x + Axi.dEta (Axi.dEta F) x)‖ ≤
        ε * K * (1 + |x.1| + |x.2.2|) ^ 2 * ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l F x‖

/-- **`B_ε` is `B_0` up to `O(ε)`** (SP 2370-2374; `b_raw = v + εHe_z` by `rawProf_eq`,
`q_ε F = ∂_qF - ε(K+1)F`, differentiability of `v` and `He_z` at `x`, the calculus identities
`∂(v + εHe_z) = ∂v + ε∂(He_z)`): for `0 ≤ ε ≤ 1`,
`‖B_εF - B_0F‖ ≤ 6 ε J(F)(J(v) + J(He_z))`. -/
def BEpsFlat : Prop :=
  ∀ (p : Params), 0 ≤ p.ε → p.ε ≤ 1 → ∀ (F : Coord → Axi.Merid) (x : Coord),
    DifferentiableAt ℝ (trainProf p) x → DifferentiableAt ℝ (raisedMerid p) x →
    ‖bEps p F x - flatB p F x‖ ≤
      6 * p.ε * chartJet F x * (chartJet (trainProf p) x + chartJet (raisedMerid p) x)

/-- **The real column difference** (SP 2375-2379): on `0 < s ≤ H/2`,
`‖colEpsR - flatReal‖ ≤ εAν^{-k}s(1+|η|)^Ne^{-κ|η|/c}`. -/
def DiffReal : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (A κ : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < A ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ (p : Params) (d : ℝ), ColReg Sig q dm dp ν₀ p d → ∀ i : Fin 2,
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H / 2 →
        ‖colEpsR p i x - flatReal p i x‖ ≤ p.ε * A * (p.ν ^ k)⁻¹ * x.1 * (1 + |x.2.2|) ^ N *
          Real.exp (-(κ * |x.2.2| / p.c))

/-- **`ColumnDifference` from its parts.** -/
theorem columnDifference_of_parts (hW : ColWeightNorm) (hFR : FlatColumnReal)
    (hFV : FlatColVanish) (hV : ColVanish) (hD : DiffReal) : ColumnDifference := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨A, κ, k, N, ν₀, hA, hκ, hν₀, hν₀1, HD⟩ := hD Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, HFR⟩ := hFR Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, HFV⟩ := hFV Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, hν₃, HV⟩ := hV Sig lam q hSig hq dm dp hdm
  obtain ⟨K, hK, HW⟩ := hW N κ hκ
  refine ⟨K * A * (1 + Sig), k + 1 + 2 * (N + 1), min ν₀ (min ν₁ (min ν₂ ν₃)),
    by positivity, lt_min hν₀ (lt_min hν₁ (lt_min hν₂ hν₃)), ?_⟩
  intro p d hreg hν hS hm i
  have h0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have h1 : p.ν ≤ ν₁ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : p.ν ≤ ν₂ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h3 : p.ν ≤ ν₃ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hνpos : 0 < p.ν := p.ν_pos
  have hεpos : 0 < p.ε := p.ε_pos
  have hν1 : p.ν ≤ 1 := h0.trans hν₀1
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hH : 0 < p.H := div_pos p.ageCut_pos hνpos
  have hMnn : 0 ≤ p.ε * A * (p.ν ^ k)⁻¹ := by positivity
  have hle := HW p.c p.H (p.ε * A * (p.ν ^ k)⁻¹) (fun x => colEps p i x - flatColumn p i x)
    hc1 hH hMnn
    (fun x hx => by
      have a := HV p d ⟨hreg, h3, hS, hm⟩ i x hx
      have b := HFV p d ⟨hreg, h2, hS, hm⟩ i x hx
      have : colEps p i x = 0 := by
        ext j
        simp [colEps, cplx, a]
      rw [this, b]
      simp)
    (fun x hx0 hx1 => by
      have e : colEps p i x - flatColumn p i x = cplx (fun y => colEpsR p i y - flatReal p i y) x := by
        rw [HFR p d ⟨hreg, h1, hS, hm⟩ i x hx0]
        ext j
        simp [colEps, cplx]
      have e2 : ‖colEps p i x - flatColumn p i x‖ = ‖colEpsR p i x - flatReal p i x‖ := by
        rw [e]
        exact liftM_norm _
      rw [e2]
      exact HD p d ⟨hreg, h0, hS, hm⟩ i x hx0 hx1)
  -- arithmetic: `(1 + H) c^{N+1} ≤ (1 + Σ) ν^{-(1 + 2(N+1))}`
  have hHle : 1 + p.H ≤ (1 + Sig) * p.ν⁻¹ := by
    have : p.H = Sig / p.ν := by simp [Params.H, hS]
    rw [this]
    have : 1 ≤ p.ν⁻¹ := one_le_inv₀ hνpos |>.2 hν1
    have h4 : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by ring
    rw [h4]
    linarith
  have hcpow : p.c ^ (N + 1) = (p.ν ^ (2 * (N + 1)))⁻¹ := by
    rw [hreg.c_eq, inv_pow, ← pow_mul]
  refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcn : 0 ≤ p.c ^ (N + 1) := by positivity
  have hpk : 0 < (p.ν ^ k)⁻¹ := by positivity
  calc K * (p.ε * A * (p.ν ^ k)⁻¹) * (1 + p.H) * p.c ^ (N + 1)
      ≤ K * (p.ε * A * (p.ν ^ k)⁻¹) * ((1 + Sig) * p.ν⁻¹) * p.c ^ (N + 1) := by gcongr
    _ = K * A * (1 + Sig) * (p.ν ^ (k + 1 + 2 * (N + 1)))⁻¹ * p.ε := by
        rw [hcpow]
        have : (p.ν ^ (k + 1 + 2 * (N + 1)))⁻¹ =
            (p.ν ^ k)⁻¹ * p.ν⁻¹ * (p.ν ^ (2 * (N + 1)))⁻¹ := by
          rw [pow_add, pow_add, pow_one, mul_inv, mul_inv]
        rw [this]
        ring

end UnforcedLeray.Short.IIb

end
