import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Near
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Affine
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Supply

/-!
# The producer of `SeqData.RepairStanding` (`ORG:C/standing`)

Source of record: `the November 2 reference manuscript` (73 pages).

`SeqData.RepairStanding` (`Concrete/ReturnRepair/Estimates.lean`, source 5115-5146, 5150-5160,
5303-5306, 5835-5859, 5926-5950) is assumed by `IIIb-D3`, `IIIb-D4`, `C/rep` and `C/cont`.
`repairStanding_of_inputs` produces it, in the order of choice of source 5835-5859: after the
reference `Pl`, `σ₀`, `m_Z` and `[d₋, d₊]` there is an integer `Kint` (that of `near:deltaN`) such
that every sequence datum with these data, whose remaining choices satisfy
`SeqData.StandingChoices D Kint dm` and whose levels satisfy the per-level background facts
`SeqData.StandingBridge D dm dp`, has the standing hypotheses.

## Inputs (the hypotheses of `repairStanding_of_inputs`)

* `NearInst.NearSolverC` : `near:inverse-comparison` under the parameter choice (3943-3951,
  4109-4124); the accepted `nearSolverC_of` (`PartIII-b:C/near/6`) of `NearFlatBoundC`,
  `NearDeltaBoundC`, `NearMaskedFreeBoundC`, composed down to other-family statements and open `C`
  ids in `Concrete/Standing/NearLayer.lean` (`nearSolverC_of_layers`; the delta branch is open
  `PartIII-b:C/near/delta`, composed in the task `PartIII-b:C/standing`);
* `NearInst.NearOpsExistC` : the actual near operators exist (3866-3914); open
  `PartIII-b:C/rep/5/1/1/1/2` (`nearOpsExistCC`);
* `SeqWardTripleSupply` : open `PartIII-b:C/ward` (4161-4303);
* `RABoundSupply` : open `PartIII-b:C/asrc/ra` (5001-5050);
* `PartIIa.NearStressMapExists` : `PartII-a:N01` (the stress map `S_μ`, 1556-1572), through the
  accepted leaves of `regimePins_stress_of`;
* `IIb.StrongRegularity` : `short-bg:strong` (`PartII-b:S3`, 2525-2562), for `hax`, `hW1` of the
  residual;
* `EACoefBound` for every source cutoff : the accepted `eaCoefBound` (`PartIII-b:C/inst/10`), a
  hypothesis only because `ReturnInst/EACoefBound.lean` and `ReturnInst/FACoefBound.lean` cannot be
  imported together (`ORG:clash-pass` step (1)).

The other pins (`lj`, `lam`, `hA`, `fA`, `body`, the split multiplier and the stress-inverse
leaves) are supplied by accepted statements in `Concrete/Standing/Affine.lean` and
`Concrete/Standing/Near.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData IsPlanarReference)

/-- **The pinned operators exist along the sequence** (source 5777-5833; the field `pins` of
`RepairStanding`), from the eleven per-field statements. -/
theorem seq_regimePins_of (D : SeqData)
    (h1 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ] Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
        NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb)
    (h2 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ o : NearInst.NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
        NearInst.IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z)
          D.K.δ ((D.level n).Scut D.K) o)
    (h3 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
        IsWeakStressInverse S (D.level n).ε (D.mu n z))
    (h4 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ R : Hsp (cOf (D.level n).ν) →L[ℝ] Hsp (cOf (D.level n).ν), NearInst.IsBodyTransport R
        (UnforcedLeray.Short.PartIIa.Teps (P := ((D.level n).params D.Pl).period)
          ((D.level n).params D.Pl).ν_pos ((D.level n).params D.Pl).ε_pos
          ((D.level n).params D.Pl).c_pos rfl ((D.mu n z : ℝ) : ℂ)))
    (h5 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ t : (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LSrc (D.level n)),
        IsWardTriple t.1 t.2.1 t.2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U
          (D.level n).pres)
    (h6 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ Lj : LStr D.Pl D.K (D.level n) →L[ℝ] AffSp D.K.as, ∀ T, affIota D.K.as (Lj T) =
        LjFun (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
          (D.level n).ε (D.mu n z) D.K.χo D.K.χy T)
    (h7 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ H : AffSp D.K.as →L[ℝ] LVel D.Pl (D.level n), ∀ A,
        (H A : Chart → Merid) =ᵐ[bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν]
          hAcoef (D.level n).ν (D.level n).ε D.K.χf (affIota D.K.as A))
    (h8 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ F : AffSp D.K.as →L[ℝ] LSrc (D.level n), ∀ A,
        (F A : Chart → Merid) =ᵐ[srcMeasure (cOf (D.level n).ν)]
          FAcoef (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A))
    (h9 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ E : AffSp D.K.as →L[ℝ] LSrc (D.level n), ∀ A,
        (E A : Chart → Merid) =ᵐ[srcMeasure (cOf (D.level n).ν)]
          EAcoef (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A))
    (h10 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ r : AffSp D.K.as →L[ℝ] LSrc (D.level n),
        IsRAOp (multOp D.Pl D.K (D.level n)) (hAOp D.Pl D.K (D.level n))
          (FAOp D.K (D.level n) (D.mu n z)) (EAOp D.K (D.level n) (D.mu n z)) r
          (affIota D.K.as) D.K.χf (D.level n).ε (D.mu n z))
    (h11 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ l : AffSp D.K.as →L[ℝ] ℝ, ∀ A, l A =
        LamFun D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl) (D.level n).ε
          (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A)) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, RegimePins D.Pl D.K (D.level n) (D.mu n z) := by
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    with n e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 z hz
  exact ⟨e1 z hz, e2 z hz, e3 z hz, e4 z hz, e5 z hz, e6 z hz, e7 z hz, e8 z hz, e9 z hz,
    e10 z hz, e11 z hz⟩

/-- **The producer of the standing hypotheses of the repair section** (source 5115-5146,
5150-5160, 5303-5306, 5777-5833, 5835-5859, 5926-5950).  For a planar reference `Pl` with
`ω ≠ 0`, `σ₀ ∈ (0, 1/4)`, `m_Z > 3/2` and `d₋ > 0` there is an integer `Kint` (the integer of
`near:deltaN`, chosen before `a, b_win`, 5841-5846) such that every sequence datum `D` with these
data, the choices `D.StandingChoices Kint dm` and the per-level background facts
`D.StandingBridge dm dp` (the bridge of `ORG:D5/skeleton` step 3) satisfies
`D.RepairStanding dm dp`.  The inputs are listed in the module docstring; the instantiated
producer is the task `PartIII-b:C/standing`. -/
theorem repairStanding_of_inputs (hNS : NearInst.NearSolverC) (hEx : NearInst.NearOpsExistC)
    (hW : SeqWardTripleSupply) (hRA : RABoundSupply)
    (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hSR : UnforcedLeray.Short.IIb.StrongRegularity)
    (hbE : ∀ (as : ℝ) (χf : ℝ → ℝ), IsSourceCutoffC χf → EACoefBound as χf)
    (Pl : PlanarData) (hP : IsPlanarReference Pl) (hω : Pl.eigenvalue.im ≠ 0) (σ₀ : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1 / 4) (mZ : ℝ) (hmZ : 3 / 2 < mZ) (dm dp : ℝ)
    (hdm : 0 < dm) :
    ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
      D.StandingChoices Kint dm → D.StandingBridge dm dp → D.RepairStanding dm dp := by
  obtain ⟨Kint, hK⟩ := seq_flatUnit_of hNS hEx Pl hP hω σ₀ hσ₀ hσ₁ mZ hmZ dm dp hdm
  refine ⟨Kint, ?_⟩
  intro D hPl hσ hmZD hc hbr
  subst hPl hσ hmZD
  have hnear' := hK D rfl rfl rfl hc.near hbr.actual hbr.inlet
  have hnear := hnear'.mono fun n h z hz => (h z hz).1
  have hflat := hnear'.mono fun n h z hz => (h z hz).2
  obtain ⟨hb, hb1, hδ, hm0, hm0d, hC0⟩ := hc.pos
  have hγ : 0 < D.Pl.eigenvalue.re := hP.eigenpair.re_pos
  have hmZ0 : 0 ≤ D.K.mZ := by linarith
  have has0 : 0 ≤ D.K.as := hc.as_pos.le
  have hact := hbr.actual
  have hnp := regimePins_near_of hEx D hP hω hσ₀ hσ₁ hmZ hdm hb hb1 hδ hm0 hm0d.le hC0 hact
  have hsp := regimePins_split_of_near D hnp
  have hsplit0 : ∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ]
      Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb := by
    filter_upwards [hsp] with n hn
    exact hn 0 ⟨by norm_num, by norm_num⟩
  have hpins := seq_regimePins_of D hsp hnp
    (regimePins_stress_of hN D hdm hω hσ₀ hσ₁ hmZ0 hC0 hact)
    (regimePins_body_of D hdm hω hσ₀ hσ₁ hact)
    (regimePins_ward_of hW D hP.eigenpair hω hσ₀ hσ₁ hm0 hc.m0_ball hC0 hmZ0 hc.chiY hact)
    (regimePins_lj_of D hω hγ hσ₀ hσ₁ hc.chiY hmZ hc.as_pos)
    (regimePins_hA_of D hω hγ hσ₀ hσ₁ hc.chiF has0 (hbE _ _ hc.chiF))
    (regimePins_fA_of D hω hγ hσ₀ hσ₁ hc.chiF has0 (hbE _ _ hc.chiF))
    (regimePins_eA_of D hω hγ hσ₀ hσ₁ hc.chiF has0 (hbE _ _ hc.chiF))
    (regimePins_rA_of hRA hSR D hdm hω hγ hσ₀ hσ₁ hc.chiF hC0 has0 hm0 hc.m0_ball hP.eigenpair
      hsplit0 hact)
    (regimePins_lam_of D hω hσ₀ hσ₁ hc.chiF has0)
  exact
    { planar := hP, gamma_pos := hγ, omega_ne := hω, sigma_pos := hσ₀, sigma_lt := hσ₁,
      dm_pos := hdm, mZ_gt := hmZ, C0_pos := hC0, b_pos := hb, b_lt := hb1, δ_pos := hδ,
      δ_lt := hc.δ_lt, m0_pos := hm0, m0_lt := hm0d, m0_ball := hc.m0_ball,
      m0_small := hc.m0_small, as_pos := hc.as_pos, as_lt := hc.as_lt, chiY := hc.chiY,
      chiF := hc.chiF, actual := hact, inlet := hbr.inlet, repairDeriv := hbr.repairDeriv,
      pins := hpins, near := hnear, flatUnit := hflat }

end UnforcedLeray.Short.PartIIIb.Concrete
