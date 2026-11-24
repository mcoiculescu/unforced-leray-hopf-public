import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Exists

/-!
# The free inverses along the concrete return sequence (source 4145, 1556-1583, 1351-1362,
1675-1677, 3888-3920, 4139-4146, 5781-5785, 5820, 5926-5950)

Source of record: `the November 2 reference manuscript` (73 pages).

For `D : SeqData` whose levels are actual for large `n` (`SeqData.IsActualLevel`: the regime
`IIb.BgRegime` with `d_n = -ν_n log ε_n ∈ [d₋, d₊]`, the exact split `IIb.ExactSplitII` with
`ρ_b = rhoB`, the exact profile of `U = V + r_b`), at large `n` and every `z ∈ [-1, 1]`, with
`μ = μ_n(z) = D.mu n z`:

* `SeqStressInverse` **(a)** : the weak stress inverse `S_μ = R_μℙ div : LStr → LVel` exists
  (`IsWeakStressInverse`, source 4145, 1556-1572, 1580-1583, 3888-3890); it feeds
  `concreteBase_isStressInverse` (`seq_isStressInverse`);
* `SeqBodyInverse` **(b)** : the body pin `IsBodyInverse (concreteBase …) ε_n μ` (source 1351-1362,
  1675-1677, 4139-4146, 5781, 5820);
* `SeqNearSplit` **(c)** : the near split pin `IsNearSplit (concreteBase …) ε_n μ δ ε_n^{-b}`
  (source 3888-3920, 5785).

The near layer `NearAt` along the sequence is not proved here (`ORG:return-concrete/near/link/seq-2`);
(b) and (c) hold for every `h : NearAt …`.

## Large levels (source 2031-2037, 5926-5950)

`inv_seq_large` : for large `n` the level is actual, `P = 2ε_nc_n ≤ 1` (`Masked.exists_period_le_one`,
`ν_n → 0`), `ε_n ≤ 1`, and `μ_n(z) ∈ [σ₀/2, (σ₀ + 1/4)/2] ⋐ (0, 1/4)` for `|z| ≤ 1`
(`mu_eventually_mem`, task `C/rinst/3`).  Hence `μ_n(z) > -1/4` and, for (c), `μ_n(z)` lies in the
compact window of `NearOpsExistC`.

## Hypotheses

Those of `Inverses/Level.lean`, and `NearInst.BodyRealForms` (`C/near/body-real/5`, accepted),
`NearInst.NearOpsExistC` (`C/near/5`).  The constants: `0 < σ₀ < 1/4` (5924-5927), `Im λ ≠ 0`
(`ν_n → 0`), `0 < d₋`, `C₀ > 0` (`ρ_b > 0`), `m_Z ≥ 0` for (a) and, for (c), the choices of
`NearOpsExistC` (`m_Z > 3/2`, `0 < b < 1`, `δ > 0`, `0 < m₀ ≤ 3d₋/11`, a planar reference).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The statements -/

/-- **(a) The weak stress inverse along the sequence** (source 4145, `free:weak-stress` 1556-1572,
bounds 1580-1583, `bg:common-body-graph` 1351-1362, 3888-3890): if the levels are actual for
large `n`, then for large `n` and every `z ∈ [-1, 1]` there is `S_μ : LStr → LVel` with
`IsWeakStressInverse S_μ ε_n μ_n(z)`. -/
def SeqStressInverse (D : SeqData) (dm dp : ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
        IsWeakStressInverse S (retEps D.Pl D.σ₀ n) (D.mu n z)

/-- **(b) The body pin along the sequence** (source 1351-1362, 1675-1677, 4139-4146, 5781, 5820):
if the levels are actual for large `n`, then for large `n`, every `z ∈ [-1, 1]` and every
invertible near layer `h`, the body inverse `R_μ = bodyG R_ε` of the concrete base is the free
response of the lifted force (`IsBodyInverse`). -/
def SeqBodyInverse (D : SeqData) (dm dp : ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ h : NearAt D.Pl D.K (D.level n) (D.mu n z),
      IsBodyInverse (concreteBase D.Pl D.K (D.level n) (D.mu n z) h) (retEps D.Pl D.σ₀ n)
        (D.mu n z)

/-- **(c) The near split pin along the sequence** (source 3888-3920, 5785): if the levels are actual
for large `n`, then for large `n`, every `z ∈ [-1, 1]` and every invertible near layer `h`,
`S_N = S_μ - S_far` for the concrete base, with `S_far` the far mask of log gap `δ` and output cut
`S = ε_n^{-b}` (`IsNearSplit`). -/
def SeqNearSplit (D : SeqData) (dm dp : ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ h : NearAt D.Pl D.K (D.level n) (D.mu n z),
      IsNearSplit (concreteBase D.Pl D.K (D.level n) (D.mu n z) h) (retEps D.Pl D.σ₀ n)
        (D.mu n z) D.K.δ ((D.level n).Scut D.K)

/-! ## 2. Large levels -/

/-- The window `[σ₀/2, (σ₀ + 1/4)/2]` of `mu_eventually_mem` is a compact subset of `(0, 1/4)`. -/
theorem inv_window_sub {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1 / 4) :
    Icc (σ₀ / 2) ((σ₀ + 1 / 4) / 2) ⊆ Ioo 0 (1 / 4) :=
  fun _ hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **Large levels** (source 2031-2037, 5926-5950): for large `n` the level is actual,
`P = 2ε_nc_n ≤ 1`, `ε_n ≤ 1`, and `μ_n(z) ∈ [σ₀/2, (σ₀ + 1/4)/2]` for `z ∈ [-1, 1]`. -/
theorem inv_seq_large (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hσ₀ : 0 < D.σ₀) (hσ₁ : D.σ₀ < 1 / 4) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n ∧ ((D.level n).params D.Pl).period ≤ 1 ∧
      retEps D.Pl D.σ₀ n ≤ 1 ∧
      ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) := by
  obtain ⟨ν₀, hν₀, hper⟩ := NearInst.Masked.exists_period_le_one hdm
  filter_upwards [hact, (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀),
    mu_eventually_mem D hω hσ₀ hσ₁] with n hL hνn hμ
  exact ⟨hL, hper _ _ dp hL.regime hνn, NearInst.Masked.eps_le_one_of_regime hL.regime, hμ⟩

/-! ## 3. (a) -/

/-- **(a) along the sequence** from the source facts of `Inverses/Level.lean`
(`StressTransportExists`, `StressMapWeakSol`, `StressPairAE`). -/
theorem seqStressInverse_of (hST : StressTransportExists) (hW : NearInst.StressMapWeakSol)
    (hPA : NearInst.StressPairAE) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ₀ : 0 < D.σ₀) (hσ₁ : D.σ₀ < 1 / 4) (hmZ : 0 ≤ D.K.mZ)
    (hC0 : 0 < D.K.C0) : SeqStressInverse D dm dp := by
  intro hact
  filter_upwards [inv_seq_large D hdm hω hσ₀ hσ₁ hact] with n hn z hz
  obtain ⟨-, hP, hε1, hμ⟩ := hn
  have hμ' : -(1 / 4) < D.mu n z := by linarith [(hμ z hz).1]
  exact exists_weakStressInverse_level hST hW hPA hε1 hP hμ' hmZ (inv_rhoB_pos hC0)

/-- **The stress pin of the concrete base along the sequence** (source 4145, 5781):
`IsStressInverse (concreteBase …) ε_n μ_n(z)` (`concreteBase_isStressInverse` with (a)). -/
theorem seq_isStressInverse (hST : StressTransportExists) (hW : NearInst.StressMapWeakSol)
    (hPA : NearInst.StressPairAE) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ₀ : 0 < D.σ₀) (hσ₁ : D.σ₀ < 1 / 4) (hmZ : 0 ≤ D.K.mZ)
    (hC0 : 0 < D.K.C0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ h : NearAt D.Pl D.K (D.level n) (D.mu n z),
      IsStressInverse (concreteBase D.Pl D.K (D.level n) (D.mu n z) h) (retEps D.Pl D.σ₀ n)
        (D.mu n z) := by
  filter_upwards [seqStressInverse_of hST hW hPA D hdm hω hσ₀ hσ₁ hmZ hC0 hact] with n hn z hz h
  exact concreteBase_isStressInverse h (hn z hz)

/-! ## 4. (b) -/

/-- **(b) along the sequence** from `TepsWeakSol`, the weak-to-graph upgrade, `SrcLiftYr`, the
cell recentring and the real forms of the body inverses (`BodyRealForms`, at the compact window
`[σ₀/2, (σ₀ + 1/4)/2]`). -/
theorem seqBodyInverse_of (hT : NearInst.TepsWeakSol) (hWF : WeakToFreeResponse)
    (hSY : SrcLiftYr) (hH : ∀ c : ℝ, 0 < c → NearInst.Masked.CellPtH c)
    (hBR : NearInst.BodyRealForms) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ₀ : 0 < D.σ₀) (hσ₁ : D.σ₀ < 1 / 4) :
    SeqBodyInverse D dm dp := by
  intro hact
  obtain ⟨ν₄, hν₄, hBR'⟩ := hBR _ isCompact_Icc (inv_window_sub hσ₀ hσ₁) dm dp hdm
  filter_upwards [inv_seq_large D hdm hω hσ₀ hσ₁ hact,
    (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₄)] with n hn hνn z hz h
  obtain ⟨hL, hP, -, hμ⟩ := hn
  have hμ' : -(1 / 4) < D.mu n z := by linarith [(hμ z hz).1]
  obtain ⟨hTe, -⟩ := hBR' _ _ hL.regime hνn _ (hμ z hz)
  exact concreteBase_isBodyInverse hT hWF hSY (hH _ (cOf_pos (retNu_pos D.Pl D.σ₀ n))) hP hμ'
    hTe h

/-! ## 5. (c) -/

/-- **(c) along the sequence** from `StressMapWeakSol`, `StressPairAE`, free weak uniqueness and the
existence of the actual near operators (`NearOpsExistC`, at the compact window
`[σ₀/2, (σ₀ + 1/4)/2]`, with the choices `m_Z > 3/2`, `0 < b < 1`, `δ > 0`, `0 < m₀ ≤ 3d₋/11`,
`C₀ > 0` and the slow age `Σ` of `D`). -/
theorem seqNearSplit_of (hW : NearInst.StressMapWeakSol) (hPA : NearInst.StressPairAE)
    (hU : ∀ (c γ ν ε μ : ℝ), 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 → 0 < μ + 1 / 4 →
      FreeWeakUniqueness c γ ν ε μ)
    (hEx : NearInst.NearOpsExistC) (D : SeqData)
    (hPl : UnforcedLeray.Blueprint.Planar.IsPlanarReference D.Pl) {dm dp : ℝ} (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ₀ : 0 < D.σ₀) (hσ₁ : D.σ₀ < 1 / 4) (hmZ : 3 / 2 < D.K.mZ)
    (hb : 0 < D.K.b) (hb1 : D.K.b < 1) (hδ : 0 < D.K.δ) (hm0 : 0 < D.K.m0)
    (hm0d : D.K.m0 ≤ 3 * dm / 11) (hC0 : 0 < D.K.C0) : SeqNearSplit D dm dp := by
  intro hact
  obtain ⟨ν₃, hν₃, hE⟩ := hEx D.Pl hPl _ isCompact_Icc (inv_window_sub hσ₀ hσ₁) D.K.mZ hmZ dm dp
    hdm D.K.b D.K.δ D.K.m0 hb hb1 hδ hm0 hm0d D.K.C0 D.K.k0 hC0 D.Sig D.Sig_pos
  filter_upwards [inv_seq_large D hdm hω hσ₀ hσ₁ hact,
    (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₃)] with n hn hνn z hz h
  obtain ⟨hL, hP, -, hμ⟩ := hn
  have hμ' : -(1 / 4) < D.mu n z := by linarith [(hμ z hz).1]
  have hex : ∃ o : NearInst.NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z)
        D.K.δ ((D.level n).Scut D.K) o :=
    hE _ _ hL.regime hνn rfl rfl _ _ _ hL.split _ (hμ z hz)
  exact concreteBase_isNearSplit hW hPA
    (hU _ _ _ _ _ (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (retNu_pos D.Pl D.σ₀ n)
      (retEps_pos D.coeff_ne n) hP (by linarith))
    hP hμ' (by linarith) (inv_rhoB_pos hC0) hex h

end UnforcedLeray.Short.PartIIIb.Concrete
