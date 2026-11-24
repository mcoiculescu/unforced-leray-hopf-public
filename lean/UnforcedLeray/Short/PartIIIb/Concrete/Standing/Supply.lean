import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Choices
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Seq

/-!
# The Ward and residual pins of the standing hypotheses (`ORG:C/standing` (a))

Source of record: `the November 2 reference manuscript` (73 pages).

The fields `ward` and `rA` of `RegimePins` come from two open `C` targets, stated here as `Prop`s
for every sequence datum (exactly the statements of the task targets, universally closed), so
that the producer of `SeqData.RepairStanding` can be compiled now:

* `SeqWardTripleSupply` : the target `seqWardTriple_exists` of `PartIII-b:C/ward`
  (`Concrete/ReturnInst/Ward/Exists.lean`; Ward fields `X, Y, f`, source 4161-4303);
* `RABoundSupply` : the target `raBoundExists` of `PartIII-b:C/asrc/ra`
  (`Concrete/ReturnInst/AffineSource/RAExists.lean`; the residual `𝔯_A`, source 5001-5050).

`regimePins_ward_of` and `regimePins_rA_of` read the two pins off them; the background inputs
`hax`, `hW1` of `raBoundExists` come from `short-bg:strong` (`IIb.StrongRegularity`, `PartII-b:S3`,
source 2525-2562) on the contraction ball of the actual levels (`seq_axi_act`, `seq_W1_act`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **The target of `PartIII-b:C/ward`** (`seqWardTriple_exists`; source 4161-4303, `ret:ward`),
for every sequence datum: with the growing eigenpair, `Im λ ≠ 0`, `σ₀ ∈ (0, 1/4)`, `m₀ > 0`,
`2m₀ < 3d₋/11`, `C₀ > 0`, `m_Z ≥ 0`, the young cutoff `χ̂_y` and actual levels, for large `n` and
`z ∈ [-1, 1]` the pinned Ward triple `(X, Y, f)` of the level exists. -/
def SeqWardTripleSupply : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode →
    D.Pl.eigenvalue.im ≠ 0 → 0 < D.σ₀ → D.σ₀ < 1 / 4 → 0 < D.K.m0 →
    2 * D.K.m0 < 3 * dm / 11 → 0 < D.K.C0 → 0 ≤ D.K.mZ → IsYoungCutoff D.K.χy →
    (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ t : (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LSrc (D.level n)),
        IsWardTriple t.1 t.2.1 t.2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U
          (D.level n).pres

/-- **The target of `PartIII-b:C/asrc/ra`** (`raBoundExists`; source 5001-5016, proof 5022-5079),
for every sequence datum: with `d₋ > 0`, `Im λ ≠ 0`, `Re λ > 0`, `σ₀ ∈ (0, 1/4)`, the source cutoff,
`C₀ > 0`, `a_s ≥ 0` and the three per-level background facts (split multiplier, axisymmetry
without swirl of `U`, a finite `W^{1,∞}` bound of `U - U_raw`), `RABoundExists D dm dp`. -/
def RABoundSupply : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), 0 < dm → D.Pl.eigenvalue.im ≠ 0 → 0 < D.Pl.eigenvalue.re →
    0 < D.σ₀ → D.σ₀ < 1 / 4 → IsSourceCutoffC D.K.χf → 0 < D.K.C0 → 0 ≤ D.K.as →
    (∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ]
      Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb) →
    (∀ᶠ n : ℕ in atTop, ∀ τ, AxiNoSwirlPt ((D.level n).U τ)) →
    (∀ᶠ n : ℕ in atTop, ∃ d : ℝ, D.W1InfAt n d) →
    RABoundExists D dm dp

/-- **The Ward triple along the sequence** (source 4161-4303; the field `ward` of `RegimePins`),
from the target of `PartIII-b:C/ward`; the young cutoff is the stream cutoff
(`IsStreamCutoff.isYoungCutoff`). -/
theorem regimePins_ward_of (hW : SeqWardTripleSupply) (D : SeqData) {dm dp : ℝ}
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) (hm0 : 0 < D.K.m0)
    (h2m : 2 * D.K.m0 < 3 * dm / 11) (hC0 : 0 < D.K.C0) (hmZ : 0 ≤ D.K.mZ)
    (hχy : IsStreamCutoff D.K.χy) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ t : (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LSrc (D.level n)),
        IsWardTriple t.1 t.2.1 t.2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U
          (D.level n).pres :=
  hW D dm dp heig hω hσ0 hσ1 hm0 h2m hC0 hmZ hχy.isYoungCutoff hact

/-- **The residual `𝔯_A` along the sequence** (source 5001-5050; the field `rA` of `RegimePins`),
from the target of `PartIII-b:C/asrc/ra`, the split multiplier at the levels, and
`short-bg:strong` (`IIb.StrongRegularity`) for the symmetry of `U` and the `W^{1,∞}` bound of
`U - U_raw` on the contraction ball (`IsActualLevel.ball`). -/
theorem regimePins_rA_of (hRA : RABoundSupply) (hSR : UnforcedLeray.Short.IIb.StrongRegularity)
    (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4)
    (hχf : IsSourceCutoffC D.K.χf) (hC0 : 0 < D.K.C0) (has : 0 ≤ D.K.as) (hm0 : 0 < D.K.m0)
    (h2m : 2 * D.K.m0 < 3 * dm / 11)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hsplit : ∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ]
      Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb)
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ r : AffSp D.K.as →L[ℝ] LSrc (D.level n),
        IsRAOp (multOp D.Pl D.K (D.level n)) (hAOp D.Pl D.K (D.level n))
          (FAOp D.K (D.level n) (D.mu n z)) (EAOp D.K (D.level n) (D.mu n z)) r
          (affIota D.K.as) D.K.χf (D.level n).ε (D.mu n z) := by
  obtain ⟨Csig, bsig, C, k, N, hb, h⟩ := hRA D dm dp hdm hω hγ hσ0 hσ1 hχf hC0 has hsplit
    (seq_axi_act (bgAxiLevels_of hSR) D hdm hm0 h2m hC0 heig hω hact)
    (seq_W1_act (bgW1Levels_of' hSR) D hdm hm0 h2m hC0 heig hω hact) hact
  filter_upwards [eventually_ge_atTop N] with n hn z hz
  obtain ⟨r, hr, -⟩ := h n hn z hz
  exact ⟨r, hr⟩

end UnforcedLeray.Short.PartIIIb.Concrete
