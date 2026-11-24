import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `RingChartRawD2` from one formula and one bound (`PartIII-b:C/rep/8/2/1/3`)

Source `the November 2 reference manuscript`
lines 5036-5045 (exact ring-chart rules `∂_r = √s(∂_q - εK)`, `∂_z = √s ∂_η`),
5460-5463 (`D²U_raw = s^{3/2}(D²_flat v + εC₂)`), 1206-1216 (the lift
`u = (R/r)(v₁, v₂ + εH)`, `K = η∂_η + 2s∂_s`, `H = (1-K)ψ`).

## Design (organizer item `ORG:C-review/ring-chart-d2`)

The earlier fourteen per-entry leaves (`NvPd2_00`, …, `RawD2Bound12`) are replaced by two
statements over all index pairs `j l` at once:

* `RingFrameD2Formula` (task `…/3/a`, pure calculus): for a profile `B` that is `C²` on `s > 0` and
  an azimuth-zero point `y = (ρ, 0, z)`, `ρ > 0`, the second Cartesian derivatives of
  `G(y) = frameL y (B (chart R τ y)) = B₀ e_r + B₁ e_z` are the table `ringFrameD2 R⁻¹ B x j l`,
  `x = chart R τ y`, in the frame basis `(e_r, e_φ, e_z) = (e₀, e₁, e₂)` at azimuth zero.  With
  `g = B∘chart`, `∂_ρ g = (Dρ B)∘chart` (`radial_chain`), `∂_z g = (Dz B)∘chart` (`axial_chain`)
  and `1/ϱ = ε√s` (`sqrt_age`):
  - `(j,l) ∈ {0,2}²`: `∂_j∂_l G = frame(D_j D_l B)` (`D₀ = Dρ`, `D₂ = Dz`, outer index outside);
  - `∂_{y₂}∂_{y₂} G = (ε√s (Dρ B)₀ - ε² s B₀) e_r + ε√s (Dρ B)₁ e_z` (`∂²_φ e_r = -e_r`);
  - `∂_{y₁}∂_{y₂} G = ∂_{y₂}∂_{y₁} G = (ε√s (Dρ B)₀ - ε² s B₀) e_φ`;
  - `∂_{y₂}∂_{y₃} G = ∂_{y₃}∂_{y₂} G = ε√s (Dz B)₀ e_φ`.
* `RingFrameD2Bound` (task `…/3/b`, profile algebra and weight bookkeeping): for `B = √s b_raw`,
  `‖ringFrameD2 ε B p j l - s^{3/2} D²_flat v(j,l)‖ ≤ C ε s^{3/2} 𝔴₃(p)` for `ε ≤ 1`, uniformly in the
  level.  (`Dρ B = s(b_ξ - ε(1+K)b)`, `Dz B = s b_η`, `Dρ Dρ B = s^{3/2}(∂_ξ - ε(2+K))(∂_ξ - ε(1+K))b`,
  `b = v + εH e_z`; every non-leading term carries `ε`.)
* `ringChartRawD2_of` assembles them with the accepted `RawProfileSmooth`, `AxisExtPd`, `ChartId`.

The Faà di Bruno jet bounds (`chartLiftJets`, `liftFactorJet`, `ringLiftPtJet`) bound `‖D^k N_v b‖`
by profile jets; they cannot produce the exact leading term `s^{3/2}D²_flat v` nor the factor `ε`
of the difference, so the formula is taken from the exact chain rules, as in the accepted
first-order siblings `nvPd0`, `nvPd1`, `nvPd2` (`Sub/PartIII-b_C_rep_8_2_1_2/N0.lean`, `N1.lean`,
`N2.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

/-- The profile `√s · b` of the ring lift `Nv R b τ = frame (B ∘ chart)`. -/
def bSqrt (b : ℝ × (ℝ × ℝ) → Merid) : ℝ × (ℝ × ℝ) → Merid := fun x => Real.sqrt x.1 • b x

/-- The radial profile operator `Dρ B = √s (∂_ξ B - ε (2s ∂_s B + η ∂_η B))`
(`∂_ρ(B∘chart) = (Dρ B)∘chart`, `ε = R⁻¹`, source 5036-5040). -/
def Drho (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) : ℝ × (ℝ × ℝ) → Merid := fun x =>
  Real.sqrt x.1 • (UnforcedLeray.Axi.dQ B x -
    ε • ((2 * x.1) • UnforcedLeray.Axi.dS B x + x.2.2 • UnforcedLeray.Axi.dEta B x))

/-- The axial profile operator `Dz B = √s ∂_η B` (`∂_z(B∘chart) = (Dz B)∘chart`, source 5038). -/
def Dz (B : ℝ × (ℝ × ℝ) → Merid) : ℝ × (ℝ × ℝ) → Merid := fun x =>
  Real.sqrt x.1 • UnforcedLeray.Axi.dEta B x

/-- **The ring-chart Hessian table** in the frame basis `(e_r, e_φ, e_z) = (e₀, e₁, e₂)` at azimuth
zero (source 5036-5045, 5463): entry `(j, l)` is `∂_{y_j}∂_{y_l}` (outer derivative `j`) of
`y ↦ frameL y (B (chart R τ y))` at the chart point `x`, `ε = R⁻¹`, `s = x.1`, `1/ϱ = ε√s`:
`(0,0) frame(Dρ Dρ B)`, `(0,2) frame(Dρ Dz B)`, `(2,0) frame(Dz Dρ B)`, `(2,2) frame(Dz Dz B)`,
`(0,1) = (1,0) = (ε√s(Dρ B)₀ - ε²s B₀) e_φ`, `(1,2) = (2,1) = ε√s (Dz B)₀ e_φ`,
`(1,1) = (ε√s(Dρ B)₀ - ε²s B₀) e_r + ε√s (Dρ B)₁ e_z`. -/
def ringFrameD2 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) (j l : Fin 3) : Space :=
  (![![merSp (Drho ε (Drho ε B) x),
        vecSp ![0, ε * Real.sqrt x.1 * (Drho ε B x) 0 - ε ^ 2 * x.1 * (B x) 0, 0],
        merSp (Drho ε (Dz B) x)],
      ![vecSp ![0, ε * Real.sqrt x.1 * (Drho ε B x) 0 - ε ^ 2 * x.1 * (B x) 0, 0],
        vecSp ![ε * Real.sqrt x.1 * (Drho ε B x) 0 - ε ^ 2 * x.1 * (B x) 0, 0,
          ε * Real.sqrt x.1 * (Drho ε B x) 1],
        vecSp ![0, ε * Real.sqrt x.1 * (Dz B x) 0, 0]],
      ![merSp (Dz (Drho ε B) x),
        vecSp ![0, ε * Real.sqrt x.1 * (Dz B x) 0, 0],
        merSp (Dz (Dz B) x)]] : Fin 3 → Fin 3 → Space) j l

/-- **(a) The second derivatives of a framed profile at azimuth zero** (pure calculus; source
5036-5045, the exact ring-chart rules, applied twice; `1/ϱ = R⁻¹√s` at `y`).  For `R > 0`, a profile
`B` of class `C²` on `{s > 0}` and `y = (ρ, 0, z)` with `ρ > 0`, every second Cartesian derivative
`∂_{y_j}∂_{y_l}` of `y' ↦ frameL y' (B (chart R τ y'))` at `y` is the entry `(j, l)` of
`ringFrameD2 R⁻¹ B (chart R τ y)`. -/
def RingFrameD2Formula : Prop :=
  ∀ (R τ : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (y : Space), 0 < R → 0 < y 0 → y 1 = 0 →
    ContDiffOn ℝ 2 B (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) → ∀ j l : Fin 3,
      physPd2 (fun y' => frameL y' (B (chart R τ y'))) j l y = ringFrameD2 R⁻¹ B (chart R τ y) j l

/-- **(b) The ring-chart Hessian table of the raw profile against the flat Hessian** (source
5460-5463, 1206-1216, 5036-5045): for `B = √s b_raw`, `b_raw = v + εH e_z`, every entry of
`ringFrameD2 ε B p` differs from `s^{3/2} D²_flat v` (`flatD2`, zero when an index is the hoop index
`1`) by at most `C ε s^{3/2} 𝔴₃(p)`, uniformly in the level for `ε ≤ 1` (`s∂_s = ∂_σ`, `σ = log s`;
the errors involve `v` to order `2`, `ψ` to order `3`, `η`-powers at most `3`). -/
def RingFrameD2Bound : Prop :=
  ∃ C : ℝ, ∀ (L : ReturnLevel), L.ε ≤ 1 → ∀ p : Chart, 0 < p.1 → ∀ j l : Fin 3,
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) p j l - p.1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L p.1 p.2 j l)‖ ≤
      C * L.ε * p.1 ^ (3 / 2 : ℝ) * trainWeight 3 L p

namespace RingChartRawD2Sub

/-- `flatD2 · · j 1 = 0` (the hoop direction is flat-trivial). -/
theorem flatD2_right_one (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) (j : Fin 3) :
    flatD2 L s x j 1 = 0 := by
  have h : flatDir 1 = 0 := by simp [flatDir]
  have h2 : (fun x' => fderiv ℝ (trainV L s) x' (flatDir 1)) = fun _ => (0 : ℝ × ℝ) := by
    funext x'; rw [h, map_zero]
  rw [flatD2, h2]
  ext i
  fin_cases i <;> simp [emb]

/-- `flatD2 · · 1 l = 0`. -/
theorem flatD2_left_one (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) (l : Fin 3) :
    flatD2 L s x 1 l = 0 := by
  have h : flatDir 1 = 0 := by simp [flatDir]
  rw [flatD2, h, map_zero]
  ext i
  fin_cases i <;> simp [emb]

/-! Entries of `ringFrameD2` (all by `rfl`). -/

theorem ringFrameD2_00 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 0 0 = merSp (Drho ε (Drho ε B) x) := rfl

theorem ringFrameD2_02 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 0 2 = merSp (Drho ε (Dz B) x) := rfl

theorem ringFrameD2_20 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 2 0 = merSp (Dz (Drho ε B) x) := rfl

theorem ringFrameD2_22 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 2 2 = merSp (Dz (Dz B) x) := rfl

theorem ringFrameD2_01 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 0 1 =
      vecSp ![0, ε * Real.sqrt x.1 * (Drho ε B x) 0 - ε ^ 2 * x.1 * (B x) 0, 0] := rfl

theorem ringFrameD2_10 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 1 0 =
      vecSp ![0, ε * Real.sqrt x.1 * (Drho ε B x) 0 - ε ^ 2 * x.1 * (B x) 0, 0] := rfl

theorem ringFrameD2_11 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 1 1 =
      vecSp ![ε * Real.sqrt x.1 * (Drho ε B x) 0 - ε ^ 2 * x.1 * (B x) 0, 0,
        ε * Real.sqrt x.1 * (Drho ε B x) 1] := rfl

theorem ringFrameD2_12 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 1 2 = vecSp ![0, ε * Real.sqrt x.1 * (Dz B x) 0, 0] := rfl

theorem ringFrameD2_21 (ε : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) :
    ringFrameD2 ε B x 2 1 = vecSp ![0, ε * Real.sqrt x.1 * (Dz B x) 0, 0] := rfl

/-- The ring lift is the framed profile `√s · b`: `Nv R b τ y = frameL y (bSqrt b (chart R τ y))`. -/
theorem Nv_eq_frame_bSqrt (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) :
    Nv R b τ = fun y => frameL y (bSqrt b (chart R τ y)) := by
  funext y
  simp only [Nv, bSqrt, map_smul]
  rfl

/-- `√s · b_raw` is `C²` on `{s > 0}`. -/
theorem contDiffOn_bSqrt (hS : RawProfileSmooth) (L : ReturnLevel) :
    ContDiffOn ℝ 2 (bSqrt (bRaw L)) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  intro x hx
  have hx0 : 0 < x.1 := hx.1
  have hsq : ContDiffAt ℝ 2 (fun x : ℝ × (ℝ × ℝ) => Real.sqrt x.1) x :=
    (Real.contDiffAt_sqrt hx0.ne').comp x contDiff_fst.contDiffAt
  have hb : ContDiffAt ℝ 2 (bRaw L) x := (hS L x hx0).of_le (by simp)
  exact (hsq.smul hb).contDiffWithinAt

end RingChartRawD2Sub

open RingChartRawD2Sub in
theorem ringChartRawD2_of (hS : RawProfileSmooth) (hA : AxisExtPd) (hC : ChartId)
    (hF : RingFrameD2Formula) (hB : RingFrameD2Bound) : RingChartRawD2 := by
  obtain ⟨C, HC⟩ := hB
  refine ⟨C, fun Pl L hε p hp0 _ j l => ?_⟩
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp0
  have hch := hC L.ε⁻¹ p hR hp0
  have hy0 : 0 < (NearInst.chartY L.ε⁻¹ p) 0 := by
    simp only [NearInst.chartY]
    exact div_pos hR hs
  have hy1 : (NearInst.chartY L.ε⁻¹ p) 1 = 0 := by simp [NearInst.chartY]
  have hax : NearInst.chartY L.ε⁻¹ p ∉ axis := fun h => hy0.ne' h.1
  have hext : physPd2 (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) j l (NearInst.chartY L.ε⁻¹ p) =
      physPd2 (Nv L.ε⁻¹ (bRaw L) (NearInst.chartTau L.ε⁻¹ p)) j l (NearInst.chartY L.ε⁻¹ p) :=
    (hA (Nv L.ε⁻¹ (bRaw L) (NearInst.chartTau L.ε⁻¹ p)) _ hax).2 j l
  rw [hext, Nv_eq_frame_bSqrt,
    hF _ _ _ _ hR hy0 hy1 (contDiffOn_bSqrt hS L) j l, hch, inv_inv, pow_zero, mul_one]
  exact HC L hε p hp0 j l

end UnforcedLeray.Short.PartIIIb.Concrete
